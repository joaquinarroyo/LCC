#ifndef __SLIST_H__
#define __SLIST_H__

#include <stddef.h>

typedef void (*FuncionVisitante) (int dato);

typedef struct SNodo {
  int dato;
  struct SNodo *sig;
  struct SNodo *ant;
} SNodo;

typedef struct DList{
    SNodo* primero;
    SNodo* ultimo;
}DList;

/**
 * Devuelve una lista vacía.
 */
DList* dlist_crear();

/**
 * Destruccion de la lista.
 */
void dlist_destruir(DList* lista);

/**
 * Determina si la lista es vacía.
 */
int dlist_vacia(DList* lista);

/**
 * Agrega un elemento al final de la lista.
 */
DList* dlist_agregar_final(DList* lista, int dato);

/**
 * Agrega un elemento al inicio de la lista.
 */
DList* dlist_agregar_inicio(DList* lista, int dato);

/**
 * Recorre la lista en ambos sentidos.
 */
DList* dlist_recorrer(DList* DList, int movimiento,FuncionVisitante imprimir);

#endif /* __SLIST_H__ */

