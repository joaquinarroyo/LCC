#include <stdio.h>
#include "dlist.h"

DList* dlist_crear(){
    DList* lista = malloc(sizeof(DList));
    lista->primero = NULL;
    lista->ultimo = NULL;
    return lista;
}

void dlist_destruir(DList* lista){
    SNodo* nodo_eliminar;
    while(lista->primero != NULL){
        nodo_eliminar = lista->primero;
        lista->primero = lista->primero->sig;
        free(nodo_eliminar);
    }
}

int dlist_vacia(DList* lista){
    return lista->primero == NULL;
}

DList* dlist_agregar_inicio(DList* lista, int dato){
    SNodo* nuevonodo = malloc(sizeof(SNodo));
    nuevonodo->dato = dato;
    nuevonodo->sig = lista->primero;
    nuevonodo->ant = NULL;
    
    if(lista->primero != NULL){
        lista->primero->ant = nuevonodo;
    }
    if(lista->ultimo = NULL){
        lista->ultimo = nuevonodo;
    }
    lista->primero = nuevonodo;
    return nuevonodo;
}

DList* dlist_agregar_final(DList* lista, int dato){
    SNodo* nuevonodo = malloc(sizeof(SNodo));
    nuevonodo->dato = dato;
    nuevonodo->sig = NULL;
    nuevonodo->ant = lista->ultimo;

    if(lista->ultimo != NULL){
        lista->ultimo->sig = nuevonodo;
    }
    if(lista->primero == NULL){
        lista->primero = nuevonodo;
    }
    lista->ultimo = nuevonodo;
    return lista;
}

DList* dlist_recorrer(DList* lista, int movimiento,FuncionVisitante imprimir){
    // 1 -> derecha 0 ->izquierda
    if(movimiento == 1 && lista->primero->sig != NULL){
        SNodo* aux = lista->primero;
        imprimir(lista->primero->sig->dato);
        lista->primero = lista->primero->sig;
        lista->ultimo = aux->ant;
    }else{
        if(lista->primero->sig == NULL){
            imprimir(lista->primero->dato);
        }
    }

    if(movimiento == 0 && lista->primero->ant != NULL){
        SNodo* aux = lista->primero;
        imprimir(lista->primero->ant->dato);
        lista->primero = lista->primero->ant;
        lista->ultimo = aux->ant;
    }else{
        if(lista->primero->ant == NULL){
            imprimir(lista->ultimo->dato);
        }
    }
    return lista;
}