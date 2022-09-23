#ifndef __SEMAFOROS_H__
#define __SEMAFOROS_H__
#include "stack.h"
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <pthread.h>
#include <wait.h>

typedef struct semaphore_t {
    int estado;
    Cstack * stack;
} sem_t ;

typedef sem_t *semaforo;

/* Función de creación de Semáforo */
semaforo sem_init();

/* Decremento del semáforo. Notar que es una función que puede llegar a bloquear
   el proceso.*/
void sem_decr(semaforo sem, int i);

/* Incremento del semáforo. */
void sem_incr(semaforo sem);

/* Destrucción de un semáforo */
void sem_destroy(semaforo sem);

#endif

