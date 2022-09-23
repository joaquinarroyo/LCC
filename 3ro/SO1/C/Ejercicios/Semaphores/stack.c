#include "stack.h"

void stack_init(Cstack * stack) {
    stack->head = stack->tail = NULL;
    pthread_mutex_init(&stack->headLock, NULL);
    pthread_mutex_init(&stack->tailLock, NULL);
}

void stack_push(Cstack *stack, int valor) {
    node *tmp = malloc(sizeof(node));
    tmp->valor = valor;
    tmp->next = NULL;
    if (stack->head == NULL) {
        pthread_mutex_lock(&stack->headLock);
        pthread_mutex_lock(&stack->tailLock);
        stack->head = tmp;
        stack->tail = tmp;
        pthread_mutex_unlock(&stack->headLock);
        pthread_mutex_unlock(&stack->tailLock);
    } else {
        pthread_mutex_lock(&stack->headLock);
        pthread_mutex_lock(&stack->tailLock);
        if (stack->tail == stack->head){
            stack->tail->next = tmp;
            stack->tail = tmp;
            stack->head->next = stack->tail;
        } else { 
        stack->tail->next = tmp;
        stack->tail = tmp;
        }
        pthread_mutex_unlock(&stack->headLock);
        pthread_mutex_unlock(&stack->tailLock);
    }
}

int stack_pop(Cstack *stack) {
    pthread_mutex_lock(&stack->headLock);
    node *tmp = stack->head;
    if (tmp == NULL) {
        return -1;
    }
    node *nuevo = tmp->next;
    int valor = tmp->valor;
    stack->head = nuevo;
    pthread_mutex_unlock(&stack->headLock);
    free(tmp);
    return valor;
}

int stack_top(Cstack *stack) {
    if (stack_vacio == 0) {
        return stack->head->valor;
    }
    return -1;
}

int stack_vacio(Cstack *stack) {
    if (stack->head == NULL) {
        return 1;
    }
    return 0;
}

/*
int main(){
    Cstack * stack = malloc(sizeof(Cstack));
    stack_init(stack);
    stack_push(stack, 1);
    stack_push(stack, 2);
    stack_push(stack, 3);
    return 0;
}
*/