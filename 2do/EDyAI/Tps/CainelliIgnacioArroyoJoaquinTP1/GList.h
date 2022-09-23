#ifndef __GLIST_H__
#define __GLIST_H__
#include <stddef.h>
#include <stdlib.h>
#include <stdio.h>

/*
Estructura que representa a un nodo de la lista
doblemente enlazada.
*/
typedef struct _GNodo {
  struct _GNodo *ant;
  void* dato;
  struct _GNodo *sig;
} GNodo;

typedef GNodo *GList;

typedef void (*Destruir) (void* dato);

typedef int (*Compara) (void* dato1, void* dato2);

typedef GList (*Algoritmo) (GList lista, Compara c);

/*
Devuelve una lista vacia.
*/
GList glist_crear();

/*
Destruye la lista.
*/
void glist_destruir(GList lista, Destruir d);

/*
Agrega un elemento al final de la lista.
*/
GList glist_agregar_final(GList lista, void* dato);

/*
Algoritmo selection sort.
*/
GList glist_selectionSort(GList lista, Compara c);

/*
Algoritmo insertion sort.
*/
GList glist_insertionSort(GList lista, Compara c);

/*
Algoritmo merge sort.
*/
GList glist_mergeSort(GList lista, Compara c);

#endif