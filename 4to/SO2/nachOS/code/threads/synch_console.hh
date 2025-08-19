#ifndef NACHOS_THREADS_SYNCHCONSOLE__HH
#define NACHOS_THREADS_SYNCHCONSOLE__HH


#include "machine/console.hh"
#include "threads/lock.hh"
#include "threads/semaphore.hh"

class SynchConsole {
public:
    SynchConsole();

    ~SynchConsole();

    void PutChar(char ch);

    char GetChar();

    void ReadDone();
    void WriteDone();

private:
    Console *console;
    Semaphore *semaphore_read;  
    Semaphore *semaphore_write;  
    Lock *lock_read;
    Lock *lock_write;
};


#endif
