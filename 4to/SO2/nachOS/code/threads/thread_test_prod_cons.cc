#include "thread_test_prod_cons.hh"
#include "system.hh"
#include "condition.hh"

#include <stdio.h>
#include <stdlib.h>
#include <cstring>
#include <string>

#define PRODUCERS 6
#define CONSUMERS 6
#define END_AFTER 100
#define BUFFER_SIZE 10

int buffer = 0;

Lock *lock;                 // Protege acceso a buffer
Condition *cond_prod;       // Condición para productores
Condition *cond_cons;       // Condición para consumidores

void Producer(void *name) {
    DEBUG('t', "Iniciando Thread %s\n", name);

    for (int i = 0; i < END_AFTER; i++) {
        lock->Acquire();

        while (buffer >= BUFFER_SIZE) {
            DEBUG('t', "Buffer lleno. Thread %s a dormir\n", name);
            cond_prod->Wait();
        }

        buffer++;
        printf("Thread %s produce, buffer: %d\n", (char *)name, buffer);
        cond_cons->Signal();

        lock->Release();
        currentThread->Yield();
    }
}

void Consumer(void *name) {
    for (int i = 0; i < END_AFTER; i++) {
        lock->Acquire();

        while (buffer <= 0) {
            DEBUG('t', "Buffer vacío. Thread %s a dormir\n", name);
            cond_cons->Wait();
        }

        buffer--;
        printf("Thread %s consume, buffer: %d\n", (char *)name, buffer);
        cond_prod->Signal();

        lock->Release();
        currentThread->Yield();
    }
}

void ThreadTestProdCons() {
    buffer = 0;

    lock = new Lock("Lock buffer");
    cond_cons = new Condition("cond_cons", lock);
    cond_prod = new Condition("cond_prod", lock);

    std::string nameCons = "consumer ";
    std::string nameProd = "producer ";

    // Crear consumidores
    for (int i = 0; i < CONSUMERS; i++) {
        char *name = new char[64];
        strncpy(name, (nameCons + std::to_string(i)).c_str(), 64);

        Thread *t = new Thread(name);
        t->Fork(Consumer, (void *)name);
    }

    // Crear productores (excepto el principal)
    for (int i = 0; i < PRODUCERS - 1; i++) {
        char *name = new char[64];
        strncpy(name, (nameProd + std::to_string(i)).c_str(), 64);

        Thread *t = new Thread(name);
        t->Fork(Producer, (void *)name);
    }

    // El hilo principal actúa como productor final
    Producer((void *)"main Producer");
}
