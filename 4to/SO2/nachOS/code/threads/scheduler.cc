/// Routines to choose the next thread to run, and to dispatch to that
/// thread.
///
/// These routines assume that interrupts are already disabled.  If
/// interrupts are disabled, we can assume mutual exclusion (since we are on
/// a uniprocessor).
///
/// NOTE: we cannot use `Lock`s to provide mutual exclusion here, since if we
/// needed to wait for a lock, and the lock was busy, we would end up calling
/// `FindNextToRun`, and that would put us in an infinite loop.
///
/// Very simple implementation -- no priorities, straight FIFO.  Might need
/// to be improved in later assignments.
///
/// Copyright (c) 1992-1993 The Regents of the University of California.
///               2016-2021 Docentes de la Universidad Nacional de Rosario.
/// All rights reserved.  See `copyright.h` for copyright notice and
/// limitation of liability and disclaimer of warranty provisions.


#include "scheduler.hh"
#include "system.hh"

#include <stdio.h>


/// Initialize the list of ready but not running threads to empty.
Scheduler::Scheduler()
{
    for (int i=0; i<MAX_PRIORITY; i++) {
        readyList[i] = new List<Thread *>;
    }
    currentPriority = MAX_PRIORITY - 1;
    nextPriority = MAX_PRIORITY - 1;
    oldPriorities = new List<int>;
    topPriorityThreads = new List<Thread *>;
}

/// De-allocate the list of ready threads.
Scheduler::~Scheduler()
{
    for (int i=0; i<MAX_PRIORITY; i++) {
        delete readyList[i];
    }
    delete oldPriorities;
    delete topPriorityThreads;
}

/// Mark a thread as ready, but not running.
/// Put it on the ready list, for later scheduling onto the CPU.
///
/// * `thread` is the thread to be put on the ready list.
void
Scheduler::ReadyToRun(Thread *thread)
{
    ASSERT(thread != nullptr);

    DEBUG('t', "Putting thread %s on ready list\n", thread->GetName());

    thread->SetStatus(READY);

    int priority = MAX_PRIORITY - 1;
    if (!topPriorityThreads->Has(thread) && currentThread == thread) {
        priority = currentPriority == 0 ? 0 : currentPriority - 1;
    }

    readyList[priority]->Append(thread);
}

/// Return the next thread to be scheduled onto the CPU.
///
/// If there are no ready threads, return null.
///
/// Side effect: thread is removed from the ready list.
Thread *
Scheduler::FindNextToRun()
{
    int i;
    for (i=MAX_PRIORITY - 1; i>0 && readyList[i]->IsEmpty(); i--);

    nextPriority = i;
    return readyList[i]->Pop();
}

/// Dispatch the CPU to `nextThread`.
///
/// Save the state of the old thread, and load the state of the new thread,
/// by calling the machine dependent context switch routine, `SWITCH`.
///
/// Note: we assume the state of the previously running thread has already
/// been changed from running to blocked or ready (depending).
///
/// Side effect: the global variable `currentThread` becomes `nextThread`.
///
/// * `nextThread` is the thread to be put into the CPU.
void
Scheduler::Run(Thread *nextThread)
{
    ASSERT(nextThread != nullptr);

    Thread *oldThread = currentThread;

#ifdef USER_PROGRAM  // Ignore until running user programs.
    if (currentThread->space != nullptr) {
        // If this thread is a user program, save the user's CPU registers.
        currentThread->SaveUserState();
        currentThread->space->SaveState();
    }
#endif

    oldThread->CheckOverflow();  // Check if the old thread had an undetected
                                 // stack overflow.

    currentThread = nextThread;  // Switch to the next thread.
    currentThread->SetStatus(RUNNING);  // `nextThread` is now running.

    DEBUG('t', "Switching from thread \"%s\" to thread \"%s\"\n",
          oldThread->GetName(), nextThread->GetName());

    // This is a machine-dependent assembly language routine defined in
    // `switch.s`.  You may have to think a bit to figure out what happens
    // after this, both from the point of view of the thread and from the
    // perspective of the “outside world”.
    currentPriority = nextPriority;
    nextPriority = MAX_PRIORITY - 1;

    SWITCH(oldThread, nextThread);

    DEBUG('t', "Now in thread \"%s\"\n", currentThread->GetName());

    // If the old thread gave up the processor because it was finishing, we
    // need to delete its carcass.  Note we cannot delete the thread before
    // now (for example, in `Thread::Finish`), because up to this point, we
    // were still running on the old thread's stack!
    if (threadToBeDestroyed != nullptr) {
        delete threadToBeDestroyed;
        threadToBeDestroyed = nullptr;
    }

#ifdef USER_PROGRAM
    if (currentThread->space != nullptr) {
        // If there is an address space to restore, do it.
        currentThread->RestoreUserState();
        currentThread->space->RestoreState();
    }
#endif
}

/// Print the scheduler state -- in other words, the contents of the ready
/// list.
///
/// For debugging.
static void
ThreadPrint(Thread *t)
{
    ASSERT(t != nullptr);
    t->Print();
}

void
Scheduler::Print()
{
    for (int i=MAX_PRIORITY - 1; i>=0; i--) {
        printf("Ready list %d contents:\n", i);
        readyList[i]->Apply(ThreadPrint);
    }
}

int
Scheduler::GetPriority(Thread *thread) {
    int i;
    for (i = MAX_PRIORITY - 1; i > 0 && !readyList[i]->Has(thread); i--);

    return i;
}

void
Scheduler::TopPriority(Thread *thread) {
    oldPriorities->Append(GetPriority(thread));
    topPriorityThreads->Append(thread);
}

void
Scheduler::ReturnPriority(Thread *thread) {
    if (!topPriorityThreads->Has(thread))
        return;

    Thread *t = nullptr;
    int p;

    while (t != thread) {
        t = topPriorityThreads->Pop();
        p = oldPriorities->Pop();

        if (thread == t) {
            currentPriority = p + 1;
        } else {
            topPriorityThreads->Append(t);
            oldPriorities->Append(p);
        }
    }
}