/// Routines to manage address spaces (memory for executing user programs).
///
/// Copyright (c) 1992-1993 The Regents of the University of California.
///               2016-2021 Docentes de la Universidad Nacional de Rosario.
/// All rights reserved.  See `copyright.h` for copyright notice and
/// limitation of liability and disclaimer of warranty provisions.


#include "address_space.hh"
#include "executable.hh"
#include "threads/system.hh"

#include <string.h>

#ifdef SWAP
#ifndef DEMAND_LOADING
ASSERT(false);
#endif
#endif

#ifdef SWAP
char* NameSwapFile(int sid) {
    if (sid == 0)
        return (char*)"SWAP.0";

    char strSid[11];
    int len = 0;
    char *swapName = new char[15]{ 'S', 'W', 'A', 'P', '.' };

    for (int aux=sid; aux > 0; aux /= 10, len++)
        strSid[len] = aux % 10 + '0';

    for (int i=0; i<len; i++)
        swapName[5 + i] = strSid[len - i - 1];
    swapName[6 + len] = '\0';

    return swapName;
}
#endif

/// First, set up the translation from program memory to physical memory.
/// For now, this is really simple (1:1), since we are only uniprogramming,
/// and we have a single unsegmented page table.
AddressSpace::AddressSpace(OpenFile *executable_file, int sid)
{
    ASSERT(executable_file != nullptr);

    exe = new Executable (executable_file);
    ASSERT(exe->CheckMagic());

    // How big is address space?

    unsigned size = exe->GetSize() + USER_STACK_SIZE;
      // We need to increase the size to leave room for the stack.
    numPages = DivRoundUp(size, PAGE_SIZE);
    size = numPages * PAGE_SIZE;
    DEBUG('t', "%d, %d\n", numPages, pages->CountClear());

    #ifdef SWAP
        char *nombre = NameSwapFile(sid);
        fileSystem->Create(nombre, size);
    #else
        ASSERT(numPages <= pages->CountClear());
    #endif

    DEBUG('a', "Initializing address space, num pages %u, size %u\n",
          numPages, size);

    // First, set up the translation.

    pageTable = new TranslationEntry[numPages];
    for (unsigned i = 0; i < numPages; i++) {
        pageTable[i].virtualPage  = i;
        #ifdef DEMAND_LOADING
            pageTable[i].physicalPage = -1;
            pageTable[i].valid        = false;
        #else
            pageTable[i].physicalPage = pages->Find();
            pageTable[i].valid        = true;
        #endif
        pageTable[i].use          = false;
        pageTable[i].dirty        = false;
        pageTable[i].readOnly     = false;
        pageTable[i].swapped      = false;
          // If the code segment was entirely on a separate page, we could
          // set its pages to be read-only.
    }

    #ifndef DEMAND_LOADING
        char *mainMemory = machine->GetMMU()->mainMemory;

        // Zero out the entire address space, to zero the unitialized data
        // segment and the stack segment.

        for (unsigned i = 0; i < numPages; i++)
            memset(mainMemory + pageTable[i].physicalPage * PAGE_SIZE, 0, PAGE_SIZE);

        // Then, copy in the code and data segments into memory.
        uint32_t codeSize = exe->GetCodeSize();
        uint32_t initDataSize = exe->GetInitDataSize();
        unsigned int physicalAddr;
        if (codeSize > 0) {
            uint32_t virtualAddr = exe->GetCodeAddr();
            DEBUG('a', "Initializing code segment, at 0x%X, size %u\n",
                virtualAddr, codeSize);
            for (unsigned i = 0; i < codeSize; i++) {
                physicalAddr = Translate(virtualAddr + i);
                exe->ReadCodeBlock(&mainMemory[physicalAddr], 1, i);
            }
        }
        if (initDataSize > 0) {
            uint32_t virtualAddr = exe->GetInitDataAddr();
            DEBUG('a', "Initializing data segment, at 0x%X, size %u\n",
                virtualAddr, initDataSize);
            for (unsigned i = 0; i < initDataSize; i++) {
                physicalAddr = Translate(virtualAddr + i);
                exe->ReadDataBlock(&mainMemory[physicalAddr], 1, i);
            }
        }
    #endif
}

/// Deallocate an address space.
///
/// Nothing for now!
AddressSpace::~AddressSpace()
{
    for (unsigned i = 0; i < numPages; i++) {
        if (pageTable[i].valid)
            pages->Clear(pageTable[i].physicalPage);
    }
    delete[] pageTable;
    #ifdef DEMAND_LOADING
        delete exe;
    #endif
}

/// Set the initial values for the user-level register set.
///
/// We write these directly into the “machine” registers, so that we can
/// immediately jump to user code.  Note that these will be saved/restored
/// into the `currentThread->userRegisters` when this thread is context
/// switched out.
void
AddressSpace::InitRegisters()
{
    for (unsigned i = 0; i < NUM_TOTAL_REGS; i++) {
        machine->WriteRegister(i, 0);
    }

    // Initial program counter -- must be location of `Start`.
    machine->WriteRegister(PC_REG, 0);

    // Need to also tell MIPS where next instruction is, because of branch
    // delay possibility.
    machine->WriteRegister(NEXT_PC_REG, 4);

    // Set the stack register to the end of the address space, where we
    // allocated the stack; but subtract off a bit, to make sure we do not
    // accidentally reference off the end!
    machine->WriteRegister(STACK_REG, numPages * PAGE_SIZE - 16);
    DEBUG('a', "Initializing stack register to %u\n",
          numPages * PAGE_SIZE - 16);
}

/// On a context switch, save any machine state, specific to this address
/// space, that needs saving.
void
AddressSpace::SaveState()
{}

/// On a context switch, restore the machine state so that this address space
/// can run.
///
/// For now, tell the machine where to find the page table.
void
AddressSpace::RestoreState()
{
    #ifdef USE_TLB
        for(unsigned int i = 0; i < TLB_SIZE; i++)
            machine->GetMMU()->tlb[i].valid = false;
    #else
        machine->GetMMU()->pageTable     = pageTable;
        machine->GetMMU()->pageTableSize = numPages;
    #endif
}

TranslationEntry
AddressSpace::GetPage(int vpn)
{
    return pageTable[vpn];
}

unsigned int AddressSpace::Translate(unsigned int virtualAddr)
{
  uint32_t page = virtualAddr / PAGE_SIZE;
  uint32_t offset = virtualAddr % PAGE_SIZE;
  return pageTable[page].physicalPage * PAGE_SIZE + offset;
}

#ifdef DEMAND_LOADING

void AddressSpace::WriteSwap(int victim) {
    int sid = pages->GetThread(victim); // Get victim thread id
    unsigned vpn = pages->GetVPN(victim); // Get victim vpn
    OpenFile *swap = fileSystem->Open(NameSwapFile(sid)); // Open victim SWAP file

    char *mainMemory = machine->GetMMU()->mainMemory;
    swap->WriteAt(&mainMemory[pageTable[vpn].physicalPage * PAGE_SIZE], PAGE_SIZE, vpn * PAGE_SIZE); // Write physical page contents on SWAP.sid
    
    pageTable[vpn].valid = false; // Set vpn entry as invalid
    pageTable[vpn].swapped = true; // Set vpn entry as swapped
    TranslationEntry *tlb = machine->GetMMU()->tlb;
    for (unsigned i = 0; i < TLB_SIZE; i++){
        if (tlb[i].physicalPage == pageTable[vpn].physicalPage && tlb[i].valid)
            tlb[i].valid = false;
    }
    delete swap;
}

void
AddressSpace::LoadPage(int vpn) {
    char *mainMemory = machine->GetMMU()->mainMemory;

    #ifdef SWAP
        if (pages->CountClear() == 0) {
            int victim = pages->PickVictim();
            int victimSid = pages->GetThread(victim);
            if (threadTable->HasKey(victimSid))
                threadTable->Get(victimSid)->space->WriteSwap(victim);
            pageTable[vpn].physicalPage = victim;
            stats->numSwaps++;
        } else {
            pageTable[vpn].physicalPage = pages->Find();
        }
        pages->Mark(pageTable[vpn].physicalPage, vpn, currentThread->sid);
    #else
        ASSERT(pages->CountClear() > 0);
        pageTable[vpn].physicalPage = pages->Find();
    #endif
    pageTable[vpn].valid = true;

    #ifdef SWAP
    
    if (pageTable[vpn].swapped) {
        OpenFile *swap = fileSystem->Open(NameSwapFile(currentThread->sid)); // Open our SWAP file
        swap->ReadAt(&mainMemory[pageTable[vpn].physicalPage * PAGE_SIZE], PAGE_SIZE, vpn * PAGE_SIZE); // Write physical page contents on SWAP.sid
        delete swap;
    } else {

    #endif

    memset(mainMemory + pageTable[vpn].physicalPage * PAGE_SIZE, 0, PAGE_SIZE);

    uint32_t codeSize = exe->GetCodeSize();
    uint32_t initDataSize = exe->GetInitDataSize();

    uint32_t codeAddr = exe->GetCodeAddr();
    uint32_t dataAddr = exe->GetInitDataAddr();

    unsigned int virtualAddr = vpn * PAGE_SIZE;
    unsigned int size = 0, sizeData;

    if (codeSize > 0 && codeSize + codeAddr > virtualAddr) {
        size = codeSize - virtualAddr;
        exe->ReadCodeBlock(
            &mainMemory[pageTable[vpn].physicalPage * PAGE_SIZE],
            PAGE_SIZE > size ? size : PAGE_SIZE,
            virtualAddr - codeAddr);
        virtualAddr += size;
    }

    if (size < PAGE_SIZE && initDataSize > 0 && dataAddr + initDataSize > virtualAddr) {
        sizeData = initDataSize - virtualAddr;
        exe->ReadDataBlock(
            &mainMemory[pageTable[vpn].physicalPage * PAGE_SIZE + size],
            PAGE_SIZE > sizeData ? size : PAGE_SIZE,
            virtualAddr - dataAddr);
    }
    #ifdef SWAP
    }

    #endif
}

#endif

