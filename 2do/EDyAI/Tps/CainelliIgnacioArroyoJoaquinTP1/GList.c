#include "GList.h"

GList glist_crear() {
  return NULL;
}

void glist_destruir(GList lista, Destruir d) {
  GNodo *nodoaEliminar;
  while (lista != NULL) {
    nodoaEliminar = lista;
    lista = lista->sig;
    nodoaEliminar->ant = NULL;
    d(nodoaEliminar->dato);
    free(nodoaEliminar);
  }
}

void intercambiar(GList nodo1, GList nodo2) {
  /*
     Recibe dos nodos e intercambia sus datos.
   */
  void *aux = nodo1->dato;
  nodo1->dato = nodo2->dato;
  nodo2->dato = aux;
}

GList glist_agregar_final(GList lista, void *dato) {
  GNodo *nuevoNodo = malloc(sizeof(GNodo));
  nuevoNodo->dato = dato;
  if (lista == NULL) {
    nuevoNodo->sig = NULL;
    nuevoNodo->ant = NULL;
    lista = nuevoNodo;
  } else {
    nuevoNodo->sig = NULL;
    GList nodo = lista;
    for (; nodo->sig != NULL; nodo = nodo->sig);
    nuevoNodo->ant = nodo;
    nodo->sig = nuevoNodo;
  }
  return lista;
}

GList glist_selectionSort(GList lista, Compara c) {
  GList nodo = lista;
  while (nodo != NULL) {
    GList menor = nodo;
    GList iterador = nodo->sig;
    int bandera = 0;
    while (iterador != NULL) {
      if ((c(menor->dato, iterador->dato)) > 0) {
        menor = iterador;
        bandera = 1;
      }
      iterador = iterador->sig;
    }
    if (bandera) {
      intercambiar(nodo, menor);
    }
    nodo = nodo->sig;
  }
  return lista;
}

GList glist_insertionSort(GList lista, Compara c) {
  GList nodo = lista;
  while (nodo != NULL) {
    GList iterador = nodo->ant;
    GList proxSig = nodo->sig;
    while (iterador != NULL) {
      if (c(iterador->dato, nodo->dato) > 0) {
        intercambiar(nodo, iterador);
        nodo = iterador;
      }
      iterador = iterador->ant;
    }
    nodo = proxSig;
  }
  return lista;
}

GList dividir(GList lista) {
  /*
     Recibe le primer nodo de una lista y devuelve el nodo que se encuentra
     a la mitad de dicha lista.
   */
  GList nodo1 = lista;
  GList nodo2 = lista;
  while (nodo1->sig != NULL && nodo1->sig->sig != NULL) {
    nodo1 = nodo1->sig->sig;
    nodo2 = nodo2->sig;
  }
  GList tmp = nodo2->sig;
  nodo2->sig = NULL;
  return tmp;
}

GList mezclar(GList nodo1, GList nodo2, Compara c) {
  /*
     Recibe dos primeros nodos de dos listas y una funcion de comparacion.
     Ordena ambas listas, y las mezcla, ya ordenadas.
   */
  if (nodo1 == NULL) {
    return nodo2;
  }
  if (nodo2 == NULL) {
    return nodo1;
  }
  if (c(nodo2->dato, nodo1->dato) > 0) {
    nodo1->sig = mezclar(nodo1->sig, nodo2, c);
    nodo1->sig->ant = nodo1;
    nodo1->ant = NULL;
    return nodo1;
  } else {
    nodo2->sig = mezclar(nodo1, nodo2->sig, c);
    nodo2->sig->ant = nodo2;
    nodo2->ant = NULL;
    return nodo2;
  }
}

GList glist_mergeSort(GList lista, Compara c) {
  if (lista == NULL || lista->sig == NULL) {
    return lista;
  }
  GList listaDividida = dividir(lista);
  lista = glist_mergeSort(lista, c);
  listaDividida = glist_mergeSort(listaDividida, c);

  return mezclar(lista, listaDividida, c);
}
