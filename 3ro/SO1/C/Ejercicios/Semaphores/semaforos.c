#include "semaforos.h"
#define CANT_THREADS 100
#define ESPERA 5000000

pthread_mutex_t count_lock[CANT_THREADS];
pthread_cond_t count_zero[CANT_THREADS];

typedef struct args_ {
    int i;
    semaforo sem;
} args;

semaforo sem_init(int i) {
    semaforo sem = malloc(sizeof(sem_t));
    Cstack * stack = malloc(sizeof(Cstack));
    sem->estado = i;
    stack_init(stack);
    sem->stack = stack;
    return sem;
}

void sem_decr(semaforo sem, int i) {
    if (sem->estado == 0) {
        stack_push(sem->stack, i);
        pthread_mutex_lock(&count_lock[i]);
    } else {
        sem->estado --;
    }
}

void sem_incr(semaforo sem) {
    if (stack_vacio(sem->stack) == 0) {
        int i = stack_pop(sem->stack);
        pthread_mutex_unlock(&count_lock[i]);
    } else {
        sem->estado ++;
    }
}

void* proceso(void* arg) {
    args *argumentos = arg;
    int i = argumentos->i;
    semaforo sem = argumentos->sem;

    for (;;) {
        sem_decr(sem, i);
        printf("Hilo %d\n", i);
        sem_incr(sem);
        usleep(random() % ESPERA);
    }
}

int main() {
    semaforo sem = sem_init(1);
    pthread_t thr[CANT_THREADS];
    args arg[CANT_THREADS];
    int i;

    for (i = 0; i < CANT_THREADS; i++) {
        arg[i].i = i;
        arg[i].sem = sem;
    }

    for (i = 0; i < CANT_THREADS; i++) {
        pthread_mutex_init(&count_lock[i], NULL);
    }

    for (i = 0; i < CANT_THREADS; i++) {
        pthread_create(&thr[i], NULL, proceso, (void* )&arg[i]);
    }

    for (int i = 0; i < CANT_THREADS; i++) {
		if (pthread_join(thr[i] , NULL) != 0){
            perror("Falló la espera de un hilo");
            exit(EXIT_FAILURE);
        }
	}

    return 0;
}