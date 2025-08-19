/// Data structures for the thread dispatcher and scheduler.
///
/// Primarily, the list of threads that are ready to run.
///
/// Copyright (c) 1992-1993 The Regents of the University of California.
///               2016-2021 Docentes de la Universidad Nacional de Rosario.
/// All rights reserved.  See `copyright.h` for copyright notice and
/// limitation of liability and disclaimer of warranty provisions.

#ifndef NACHOS_THREADS_CHANNEL__HH
#define NACHOS_THREADS_CHANNEL__HH

#include "thread.hh"
#include "lock.hh"
#include "condition.hh"

class Channel {
public:
    Channel(const char* debugName);
    ~Channel();

    void Send(int msg);
    void Receive(int* msg);

private:
    Lock *receiverLock;
    Lock *senderLock;

    int buffer;
    const char *name;

    Semaphore *syncSem1;
    Semaphore *syncSem2;
};

#endif
