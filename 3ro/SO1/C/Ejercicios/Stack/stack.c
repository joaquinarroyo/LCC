#include "stack.h"

void stack_init(Cstack * stack) {
    node *tmp = malloc(sizeof(node));
    tmp->next = NULL;
    stack->head = stack->tail = tmp;
    pthread_mutex_init(&stack->headLock, NULL);
    pthread_mutex_init(&stack->tailLock, NULL);
}

void stack_push(Cstack *stack, int valor) {
    node * tmp = malloc(sizeof(node));
    tmp->valor = valor;
    tmp->next = NULL;

    pthread_mutex_lock(&stack->tailLock);
    stack->tail->next = tmp;
    stack->tail = tmp;
    pthread_mutex_unlock(&stack->tailLock);
}

void stack_pop(Cstack *stack) {
    pthread_mutex_lock(&stack->headLock);
    node *tmp = stack->head;
    node *nuevo = tmp->next;
    if (nuevo == NULL) {
        pthread_mutex_unlock(&stack->headLock);
    }
    int valor = nuevo->valor;
    stack->head = nuevo;
    pthread_mutex_unlock(&stack->headLock);
    free(tmp);
}

int stack_top(Cstack *stack) {
    return stack->head->valor;
}