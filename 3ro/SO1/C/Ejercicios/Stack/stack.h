#ifndef __STACK_H__
#define __STACK_H__
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <pthread.h>

typedef struct node_t {
    int valor;
    struct _node_t *next;
} node;

typedef struct stack_t {
    node *head;
    node *tail;
    pthread_mutex_t headLock;
    pthread_mutex_t tailLock;
} Cstack;

void stack_init(Cstack * stack);
void stack_destroy();

void stack_push(struct stack_t  * stack, int valor);
void stack_pop(struct stack_t * stack);
int stack_top(struct stack_t * stack);

#endif
