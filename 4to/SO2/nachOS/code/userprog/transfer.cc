/// Copyright (c) 2019-2021 Docentes de la Universidad Nacional de Rosario.
/// All rights reserved.  See `copyright.h` for copyright notice and
/// limitation of liability and disclaimer of warranty provisions.


#include "transfer.hh"
#include "lib/utility.hh"
#include "threads/system.hh"

#define TLB_TRIES 4

void ReadBufferFromUser(int userAddress, char *outBuffer,
                        unsigned byteCount)
{
    ASSERT(userAddress != 0);
    ASSERT(outBuffer != nullptr);
    ASSERT(byteCount != 0);
    // ASSERT(sizeof(outBuffer) >= byteCount);

    unsigned count = 0;
    do {
        int temp;
        count++;
        #ifdef USE_TLB
            int j = TLB_TRIES;
            while (j > 0 && !machine->ReadMem(userAddress, 1, &temp))
                j--;
            userAddress++;
            ASSERT(j != 0);
        #else
            ASSERT(machine->ReadMem(userAddress++, 1, &temp));
        #endif
        *outBuffer = (unsigned char) temp;
        outBuffer++;
    } while (count < byteCount);
}

bool ReadStringFromUser(int userAddress, char *outString,
                        unsigned maxByteCount)
{
    ASSERT(userAddress != 0);
    ASSERT(outString != nullptr);
    ASSERT(maxByteCount != 0);

    unsigned count = 0;
    do {
        int temp;
        count++;
        #ifdef USE_TLB
            int j = TLB_TRIES;
            while (j > 0 && !machine->ReadMem(userAddress, 1, &temp))
                j--;
            userAddress++;
            ASSERT(j != 0);
        #else
            ASSERT(machine->ReadMem(userAddress++, 1, &temp));
        #endif
        *outString = (unsigned char) temp;
    } while (*outString++ != '\0' && count < maxByteCount);

    return *(outString - 1) == '\0';
}

void WriteBufferToUser(const char *buffer, int userAddress,
                       unsigned byteCount)
{
    ASSERT(userAddress != 0);
    ASSERT(buffer != nullptr);
    ASSERT(byteCount != 0);
    // ASSERT(sizeof (buffer) / sizeof (char) >= byteCount); Ver si esto funciona bien

    for (unsigned count = 0; count < byteCount; count++) {
        #ifdef USE_TLB
            int j = TLB_TRIES;
            while (j > 0 && !machine->WriteMem(userAddress, 1, (int)buffer[count]))
                j--;
            userAddress++;
            ASSERT(j != 0);
        #else
            ASSERT(machine->WriteMem(userAddress++, 1, (int)buffer[count]));
        #endif
    }
}

void WriteStringToUser(const char *string, int userAddress)
{
    ASSERT(userAddress != 0);
    ASSERT(string != nullptr);

    unsigned count = 0;

    do {
        #ifdef USE_TLB
            int j = TLB_TRIES;
            while (j > 0 && !machine->WriteMem(userAddress, 1, string[count]))
                j--;
            userAddress++;
            count++;
            ASSERT(j != 0);
        #else
            ASSERT(machine->WriteMem(userAddress++, 1, string[count++]));
        #endif
    } while (string[count] != '\0');
}
