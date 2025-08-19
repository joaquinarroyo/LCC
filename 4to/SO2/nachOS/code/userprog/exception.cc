/// Entry points into the Nachos kernel from user programs.
///
/// There are two kinds of things that can cause control to transfer back to
/// here from user code:
///
/// * System calls: the user code explicitly requests to call a procedure in
///   the Nachos kernel.  Right now, the only function we support is `Halt`.
///
/// * Exceptions: the user code does something that the CPU cannot handle.
///   For instance, accessing memory that does not exist, arithmetic errors,
///   etc.
///
/// Interrupts (which can also cause control to transfer from user code into
/// the Nachos kernel) are handled elsewhere.
///
/// For now, this only handles the `Halt` system call.  Everything else core-
/// dumps.
///
/// Copyright (c) 1992-1993 The Regents of the University of California.
///               2016-2021 Docentes de la Universidad Nacional de Rosario.
/// All rights reserved.  See `copyright.h` for copyright notice and
/// limitation of liability and disclaimer of warranty provisions.


#include "transfer.hh"
#include "syscall.h"
#include "args.hh"
#include "filesys/open_file.hh"
#include "filesys/directory_entry.hh"
#include "threads/system.hh"
#include "machine/translation_entry.hh"
#include "machine/mmu.hh"

struct Arguments {
    char* filename;
    char** args;
};

#include <stdio.h>

#define FILE_SIZE 256

static void
IncrementPC()
{
    unsigned pc;

    pc = machine->ReadRegister(PC_REG);
    machine->WriteRegister(PREV_PC_REG, pc);
    pc = machine->ReadRegister(NEXT_PC_REG);
    machine->WriteRegister(PC_REG, pc);
    pc += 4;
    machine->WriteRegister(NEXT_PC_REG, pc);
}

/// Do some default behavior for an unexpected exception.
///
/// NOTE: this function is meant specifically for unexpected exceptions.  If
/// you implement a new behavior for some exception, do not extend this
/// function: assign a new handler instead.
///
/// * `et` is the kind of exception.  The list of possible exceptions is in
///   `machine/exception_type.hh`.
static void
DefaultHandler(ExceptionType et)
{
    int exceptionArg = machine->ReadRegister(2);

    fprintf(stderr, "Unexpected user mode exception: %s, arg %d.\n",
            ExceptionTypeToString(et), exceptionArg);
    ASSERT(false);
}

char *readFilename(int filenameAddr) {
    if (filenameAddr == 0) {
        DEBUG('e', "Error: address to filename string is null.\n");
    }

    char *filename = new char[FILE_NAME_MAX_LEN + 1];
    if (!ReadStringFromUser(filenameAddr,
                            filename, sizeof filename)) {
        DEBUG('e', "Error: filename string too long (maximum is %u bytes).\n",
                FILE_NAME_MAX_LEN);
    }
    return filename;
}

void
StartProc(void *args)
{
    currentThread->space->InitRegisters();  // Set the initial register values.
    currentThread->space->RestoreState();   // Load page table register.

    if (args != nullptr)
    {
        unsigned argc = WriteArgs((char**)args);
        machine->WriteRegister(4, argc);
        int sp = machine->ReadRegister(STACK_REG);
        machine->WriteRegister(5, sp);
        machine->WriteRegister(STACK_REG, sp - 24);
    }
    machine->Run();  // Jump to the user progam.
    ASSERT(false);   // `machine->Run` never returns; the address space
                     // exits by doing the system call `Exit`.
}

/// Handle a system call exception.
///
/// * `et` is the kind of exception.  The list of possible exceptions is in
///   `machine/exception_type.hh`.
///
/// The calling convention is the following:
///
/// * system call identifier in `r2`;
/// * 1st argument in `r4`;
/// * 2nd argument in `r5`;
/// * 3rd argument in `r6`;
/// * 4th argument in `r7`;
/// * the result of the system call, if any, must be put back into `r2`.
///
/// And do not forget to increment the program counter before returning. (Or
/// else you will loop making the same system call forever!)
static void
SyscallHandler(ExceptionType _et)
{
    int scid = machine->ReadRegister(2);

    #ifdef FILESYS
    int sector = currentThread->GetCurrentDir();
    #endif
    switch (scid) {

        case SC_HALT:
            DEBUG('e', "Shutdown, initiated by user program.\n");
            interrupt->Halt();
            break;

        case SC_CREATE: {
            DEBUG('e', "`Create` requested\n");
            char *filename = readFilename(machine->ReadRegister(4));
            #ifdef FILESYS
            int success = fileSystem->Create(filename, FILE_SIZE, sector);
            #else
            int success = fileSystem->Create(filename, FILE_SIZE);
            #endif
            if (success == 0) {
                DEBUG('e', "Error: couldn't create file");
                machine->WriteRegister(2, -1);
            } else {
                DEBUG('e', "`Create` done for file `%s`.\n", filename);
                machine->WriteRegister(2, 0);
            }
            delete filename;
            break;
        }

        case SC_REMOVE: {
            DEBUG('e', "`Remove` requested\n");
            char *filename = readFilename(machine->ReadRegister(4));
            #ifdef FILESYS
            int res = !fileSystem->Remove(filename, sector);
            #else
            int res = !fileSystem->Remove(filename);
            #endif
            if (res) {
                DEBUG('e', "Error: couldn't remove, file doesn't exist");
                machine->WriteRegister(2, 1);
            } else {
                DEBUG('e', "`Remove` done for file `%s`.\n", filename);
                machine->WriteRegister(2, 0);
            }
            delete filename;
            break;
        }

        case SC_EXIT: {
            DEBUG('e', "`Exit` requested\n");
            int status = machine->ReadRegister(4);
            if (status == 0) {
                DEBUG('e', "Exited normally\n");
            }else {
                DEBUG('e', "Abnormal exit\n");
            }
            
            currentThread->Finish();
            break;
        }

        case SC_WRITE: {
            DEBUG('e', "`Write` requested\n");
            int stringAddr = machine->ReadRegister(4);
            int size = machine->ReadRegister(5);
            OpenFileId id = machine->ReadRegister(6);

            int res = -1;
            if (!stringAddr)
                DEBUG('e', "Error: address to string is null.\n");
            else if (size < 0)
                DEBUG('e', "Error: invalid string size.\n");
            else if (id < CONSOLE_OUTPUT)
                DEBUG('e', "Error: invalid file descriptor.\n");
            else {
                char str[size];

                ReadBufferFromUser(stringAddr, str, size);

                if (id == CONSOLE_OUTPUT) {
                    for (int i = 0; i < size; i++) {
                        synchConsole->PutChar(str[i]);
                    }
                }else if (currentThread->fileTable->HasKey(id)) {
                    res = currentThread->fileTable->Get(id)->Write(str, size);
                }else {
                    DEBUG('e', "Error: no file with that id");
                }
            }

            machine->WriteRegister(2, res);
            break;
        }

        case SC_READ: {
            DEBUG('e', "`Read` requested\n");
            int usrAddr = machine->ReadRegister(4);
            int size = machine->ReadRegister(5);
            OpenFileId id = machine->ReadRegister(6);
            int i = -1;
            if (!usrAddr)
                DEBUG('e', "Error: address to usr is null.\n");
            else if (size < 0)
                DEBUG('e', "Error: invalid size.\n");
            else if (id == CONSOLE_OUTPUT)
                DEBUG('e', "Error: invalid file descriptor.\n");
            else {
                char str[size+1];

                if (id == CONSOLE_INPUT) {
                    for(i = 0; i < size; i++) {
                        str[i] = synchConsole->GetChar();
                    }
                    str[i] = '\0';
                }else if (currentThread->fileTable->HasKey(id)) {
                    i = currentThread->fileTable->Get(id)->Read(str, size);
                    str[i] = '\0';
                }else {
                    DEBUG('e', "Error: no file with that id");
                }
                
                WriteStringToUser(str, usrAddr);
            }
            
            machine->WriteRegister(2, i);
            DEBUG('e', "`Read` Completed\n");

            break;
        }

        case SC_CLOSE: {
            DEBUG('e', "`Close` requested\n");
            OpenFileId fid = machine->ReadRegister(4);
            int status = -1;

            if (fid < 0)
                DEBUG('e',"Invalid file id");
            else if (currentThread->fileTable->HasKey(fid)) {
                OpenFile* item = currentThread->fileTable->Remove(fid);
                delete item;
                status = 0;
            }else {
                DEBUG('e', "No file with such id\n");
            }
            machine->WriteRegister(2, status);
            break;
        }

        case SC_OPEN: {
            DEBUG('e', "`Open` requested\n");
            char *filename = readFilename(machine->ReadRegister(4));
            #ifdef FILESYS
            OpenFile* fid = fileSystem->Open(filename, currentThread->GetCurrentDir());
            #else
            OpenFile* fid = fileSystem->Open(filename);
            #endif
            OpenFileId opfid = -1;

            if (fid != nullptr) {
                opfid = currentThread->fileTable->Add(fid);
                DEBUG('e', "`Open` requested for opfid %u.\n", opfid);
            }else {
                DEBUG('e', "Couldn't open file.\n");
                opfid = -1;
            }

            machine->WriteRegister(2, opfid);
            break;
        }

        case SC_JOIN: {
            DEBUG('e', "`Join` requested\n");
            SpaceId id = machine->ReadRegister(4);

            if (!threadTable->HasKey(id)) {
                DEBUG('e', "No thread with such key\n");
                machine->WriteRegister(2, -1);
            }else {
                DEBUG('e', "Started to join thread: %d\n", id);
                threadTable->Get(id)->Join();
                machine->WriteRegister(2, 0);
            }
            break;
        }

        case SC_EXEC: {
            DEBUG('e', "`Exec` requested\n");
            char *filename = readFilename(machine->ReadRegister(4));
            int argsAddr = machine->ReadRegister(5);
            int joinable = machine->ReadRegister(6);

            if(filename != nullptr) {
                char** savedArgs = SaveArgs(argsAddr);
                currentThread->SaveUserState();
                Thread* userThread = new Thread(filename, joinable);
                #ifdef FILESYS
                userThread->Cd(currentThread->GetCurrentDir());
                OpenFile *executable = fileSystem->Open(filename, DIRECTORY_SECTOR);
                #else
                OpenFile *executable = fileSystem->Open(filename);
                #endif
                if (executable == nullptr) {
                    DEBUG('e', "Unable to open file %s\n", filename);
                    machine->WriteRegister(2, -1);
                } else {
                    userThread->space = new AddressSpace(executable, userThread->sid);
                    userThread->Fork(StartProc, (void *) savedArgs);
                    machine->WriteRegister(2, userThread->sid);
                    #ifdef FILESYS
                    if (currentThread->GetCurrentDir() != DIRECTORY_SECTOR)
                        fileSystem->Remove(filename, currentThread->GetCurrentDir());
                    #endif
                    #ifndef DEMAND_LOADING
                        delete executable;
                    #endif
                }
            } else {
                machine->WriteRegister(2, -1);
            }
            break;
        }
        
        case SC_PS: {
            DEBUG('e', "`Print Scheduler` requested\n");
            scheduler->Print();
            break;
        }

        case SC_SP: {
            DEBUG('e', "Stats print requested\n");
            stats->Print();
            break;
        }

        case SC_CD: {
            #ifdef FILESYS
                DEBUG('e', "cd requested\n");
                int pathDir = machine->ReadRegister(4);
                char *path = readFilename(pathDir);
                int newSector = fileSystem->Cd(path);
                DEBUG('f', "cd to sector %d\n", newSector);
                if(newSector != -1)
                    currentThread->Cd(newSector);
                machine->WriteRegister(2, newSector);
            #endif
            break;
        }

        case SC_LS: {
            #ifdef FILESYS
                DEBUG('e', "ls requested\n");
                fileSystem->Ls();
            #endif
            break;
        }

        case SC_MKDIR: {
            #ifdef FILESYS
                DEBUG('e', "mkdir requested\n");
                int nameAddr = machine->ReadRegister(4);
                char *name = readFilename(nameAddr);
                int success = fileSystem->Mkdir(name);
                machine->WriteRegister(2, success == 0 ? -1 : 1);
                DEBUG('e', "mkdir res: %d\n", success);
            #endif
            break;
        }

        default:
            fprintf(stderr, "Unexpected system call: id %d.\n", scid);
            ASSERT(false);

    }

    IncrementPC();
}
#ifdef USE_TLB

    static long tlbOffset = 0;
    static void PageFaultHandler(ExceptionType _et) {
        int vAddr = machine->ReadRegister(BAD_VADDR_REG);
        int vpn = vAddr / PAGE_SIZE;
        ASSERT(vpn >= 0);
        stats->numPageFaults++;
        TranslationEntry e = currentThread->space->GetPage(vpn);
        
        #ifdef DEMAND_LOADING
            if(!e.valid)
                currentThread->space->LoadPage(vpn);
        #endif

        tlbOffset %= TLB_SIZE;
        machine->GetMMU()->tlb[tlbOffset] = e;
        tlbOffset++;
    }

    static void ReadOnlyHandler(ExceptionType _et) {
        DEBUG('b', "Read only exception\n");
        ASSERT(false);
    }
#endif
/// By default, only system calls have their own handler.  All other
/// exception types are assigned the default handler.
void
SetExceptionHandlers()
{
    machine->SetHandler(NO_EXCEPTION,            &DefaultHandler);
    machine->SetHandler(SYSCALL_EXCEPTION,       &SyscallHandler);
    #ifdef USE_TLB
        machine->SetHandler(PAGE_FAULT_EXCEPTION,    &PageFaultHandler);
        machine->SetHandler(READ_ONLY_EXCEPTION,     &ReadOnlyHandler);
    #else
        machine->SetHandler(PAGE_FAULT_EXCEPTION,    &DefaultHandler);
        machine->SetHandler(READ_ONLY_EXCEPTION,     &DefaultHandler);
    #endif
    machine->SetHandler(BUS_ERROR_EXCEPTION,     &DefaultHandler);
    machine->SetHandler(ADDRESS_ERROR_EXCEPTION, &DefaultHandler);
    machine->SetHandler(OVERFLOW_EXCEPTION,      &DefaultHandler);
    machine->SetHandler(ILLEGAL_INSTR_EXCEPTION, &DefaultHandler);
}
