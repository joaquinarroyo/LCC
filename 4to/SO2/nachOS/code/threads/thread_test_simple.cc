/// Copyright (c) 1992-1993 The Regents of the University of California.
///               2007-2009 Universidad de Las Palmas de Gran Canaria.
///               2016-2021 Docentes de la Universidad Nacional de Rosario.
/// All rights reserved.  See `copyright.h` for copyright notice and
/// limitation of liability and disclaimer of warranty provisions.


#include "thread_test_simple.hh"
#include "system.hh"
#include "semaphore.hh"

#include <stdio.h>
#include <string.h>

static Semaphore *sem;          // Semáforo para controlar la sección crítica
static Semaphore *doneSem;      // Semáforo para sincronizar la finalización de los hilos
static int activeThreads = 0;   // Contador de hilos activos

void
SimpleThread(void *name_)
{
    char *name = (char *) name_;

    #ifdef SEMAPHORE_TEST
        sem->P();
        DEBUG('s', "Thread %s executes sem->P()\n", name);
    #endif

    for (unsigned num = 0; num < 5; num++) {
        printf("*** Thread `%s` is running: iteration %u\n", name, num);
        currentThread->Yield();
    }

    #ifdef SEMAPHORE_TEST
        sem->V();
        DEBUG('s', "Thread %s executes sem->V()\n", name);
    #endif

    printf("!!! Thread `%s` has finished\n", name);

    // Decrementa el contador de hilos activos y libera el semáforo de finalización
    doneSem->P();
    activeThreads--;
    doneSem->V();
}

/// Set up a ping-pong between several threads.
///
/// Do it by launching one thread which calls `SimpleThread`, and finally
/// calling `SimpleThread` on the current thread.
void
ThreadTestSimple()
{
    // Inicializa los semáforos
    #ifdef SEMAPHORE_TEST
        sem = new Semaphore("Sem", 5);
    #else
        sem = NULL;
    #endif
    doneSem = new Semaphore("DoneSem", 1);

    // Crea los hilos secundarios
    char *name5 = new char[64];
    strncpy(name5, "5th", 64);
    Thread *newThread5 = new Thread(name5);

    char *name4 = new char[64];
    strncpy(name4, "4th", 64);
    Thread *newThread4 = new Thread(name4);

    char *name3 = new char[64];
    strncpy(name3, "3rd", 64);
    Thread *newThread3 = new Thread(name3);

    char *name2 = new char[64];
    strncpy(name2, "2nd", 64);
    Thread *newThread2 = new Thread(name2);

    // Incrementa el contador de hilos activos
    doneSem->P();
    activeThreads += 5;
    doneSem->V();

    // Lanza los hilos secundarios
    newThread5->Fork(SimpleThread, (void *)name5);
    newThread4->Fork(SimpleThread, (void *)name4);
    newThread3->Fork(SimpleThread, (void *)name3);
    newThread2->Fork(SimpleThread, (void *)name2);

    // Ejecuta el hilo principal
    SimpleThread((void *)"1st");

    // Espera a que todos los hilos secundarios terminen
    while (true) {
        doneSem->P();
        if (activeThreads == 0) {
            doneSem->V();
            break;
        }
        doneSem->V();
        currentThread->Yield();
    }

    // Limpia los semáforos
    #ifdef SEMAPHORE_TEST
        delete sem;
    #endif
    delete doneSem;
}