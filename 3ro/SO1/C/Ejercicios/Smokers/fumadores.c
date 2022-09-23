/* Se incluyen las librerías necesarias*/
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include <semaphore.h>

/* Estructura para los argumentos */
typedef struct _argument {
  sem_t tabaco;
  sem_t papel;
  sem_t fosforos;
  sem_t otra_vez;
  sem_t entro1;
  sem_t entro2;
  sem_t entro3;
} args_t;

void agente(void * _args)
{
  args_t *args = (args_t *) _args;
  for (;;) {
    int caso = random() % 3;
    sem_wait(&args->otra_vez);
    switch (caso) {
      case 0:
          sem_post(&args->entro1);
          sem_post(&args->tabaco);
          sem_post(&args->papel);
          break;
      case 1:
          sem_post(&args->entro2);
          sem_post(&args->fosforos);
          sem_post(&args->tabaco);
          break;
      case 2:
          sem_post(&args->entro3);
          sem_post(&args->papel);
          sem_post(&args->fosforos);
          break;
    }
  }
  /* Dead code */
  return;
}

void fumar(int fumador)
{
    printf("Fumador %d: *fuma* Puf! Puf! Puf!\n", fumador);
    sleep(3);
}

void *fumador1(void *_arg)
{
  args_t *args = (args_t *) _arg;
  printf("Fumador 1: Hola!\n");
  for (;;) {
    sem_wait(&args->entro1);
    sem_wait(&args->tabaco);
    sem_wait(&args->papel);
    fumar(1);
    sem_post(&args->otra_vez);
  }
  /* Dead code*/
  pthread_exit(0);
}

void *fumador2(void *_arg)
{
  args_t *args = (args_t *) _arg;
  printf("Fumador 2: Hola!\n");
  for (;;) {
    sem_wait(&args->entro2);
    sem_wait(&args->fosforos);
    sem_wait(&args->tabaco);
    fumar(2);
    sem_post(&args->otra_vez);
  }
  /* Dead code*/
  pthread_exit(0);
}

void *fumador3(void *_arg)
{
  args_t *args = (args_t *) _arg;
  printf("Fumador 3: Hola!\n");
  for (;;) {
    sem_wait(&args->entro3);
    sem_wait(&args->papel);
    sem_wait(&args->fosforos);
    fumar(3);
    sem_post(&args->otra_vez);
  }
  /* Dead code*/
  pthread_exit(0);
}

int main()
{
  /* Memoria para los hilos */
  pthread_t s1, s2, s3;
  /* Memoria dinámica para los argumentos */
  args_t *args = malloc(sizeof(args_t));

  /* Se inicializan los semáforos */
  sem_init(&args->tabaco, 0, 0);
  sem_init(&args->papel, 0, 0);
  sem_init(&args->fosforos, 0, 0);
  sem_init(&args->otra_vez, 0, 1);
  sem_init(&args->entro1, 0, 0);
  sem_init(&args->entro2, 0, 0);
  sem_init(&args->entro3, 0, 0);
  /************/

  /* Se inicializan los hilos*/
  pthread_create(&s1, NULL, fumador1, (void*)args);
  pthread_create(&s2, NULL, fumador2, (void*)args);
  pthread_create(&s3, NULL, fumador3, (void*)args);
  /************/

  /* Y el agente que provee con los elemetos*/
  agente((void *)args);
  /************/

  return 0;
}
