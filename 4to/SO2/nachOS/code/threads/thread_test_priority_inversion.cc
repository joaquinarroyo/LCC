#include "thread_test_priority_inversion.hh"
#include "system.hh"
#include "lock.hh"
#include <stdio.h>

Lock *testLock;

void LowPriorityThread(void *arg) {
    printf("Low priority thread starting\n");
    testLock->Acquire();
    printf("Low priority thread acquired lock\n");
    for (int i = 0; i < 5; i++) {
        currentThread->Yield();
    }
    printf("Low priority thread releasing lock\n");
    testLock->Release();
    currentThread->Finish(0);
}

void HighPriorityThread(void *arg) {
    printf("High priority thread starting\n");
    testLock->Acquire();
    printf("High priority thread acquired lock\n");
    testLock->Release();
    printf("High priority thread finished\n");
    currentThread->Finish(0);
}

void ThreadTestPriorityInversion() {
    printf("Starting ThreadTestPriorityInversion\n");

    testLock = new Lock("Test Lock");

    Thread *lowPriority = new Thread("Low Priority Thread", true);
    Thread *highPriority = new Thread("High Priority Thread", true);

    // Elevar temporalmente la prioridad del hilo de alta prioridad
    scheduler->TopPriority(highPriority);

    lowPriority->Fork(LowPriorityThread, nullptr);
    currentThread->Yield(); // Asegurar que el hilo de baja prioridad adquiera el lock primero
    highPriority->Fork(HighPriorityThread, nullptr);

    lowPriority->Join();
    highPriority->Join();

    // Restaurar la prioridad original del hilo de alta prioridad
    scheduler->ReturnPriority(highPriority);

    delete testLock;

    printf("ThreadTestPriorityInversion finished\n");
}