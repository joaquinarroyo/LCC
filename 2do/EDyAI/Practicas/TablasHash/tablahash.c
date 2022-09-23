#include "tablahash.h"

/**
 * Crea una nueva tabla Hash vacía, con la capacidad dada.
 */
TablaHash *tablahash_crear(unsigned capacidad, FuncionHash hash) {
  // Pedimos memoria para la estructura principal y las casillas.
  TablaHash *tabla = malloc(sizeof(TablaHash));
  tabla->hash = hash;
  tabla->capacidad = capacidad;
  tabla->tabla = malloc(sizeof(CasillaHash) * capacidad);
  tabla->numElems = 0;

  // Inicializamos las casillas con datos nulos.
  for (unsigned idx = 0; idx < capacidad; ++idx) {
    tabla->tabla[idx].datos = malloc(sizeof(SNodo));
    tabla->tabla[idx].clave = NULL;
    tabla->tabla[idx].datos->dato = NULL;
  }
  return tabla;
}

/**
 * Inserta el dato en la tabla, asociado a la clave dada.
 */
void tablahash_insertar(TablaHash * tabla, void *clave, void *dato) {
  // Calculamos la posición de la clave dada, de acuerdo a la función hash.
  unsigned idx = tabla->hash(clave);
  idx = idx % tabla->capacidad;

  if (tabla->tabla[idx].clave == NULL) {
    tabla->tabla[idx].clave = clave;
    tabla->tabla[idx].datos->dato = dato;
    tabla->tabla[idx].datos->sig = NULL;
  } else {
    SList nodo = tabla->tabla[idx].datos;
    while (nodo->sig != NULL) {
      nodo = nodo->sig;
    }
    nodo->sig = malloc(sizeof(SNodo));
    nodo->sig->dato = dato;
    nodo->sig->sig = NULL;
  }
  tabla->numElems++;
}

/**
 * Busca un elemento dado en la tabla, y retorna un puntero al mismo.
 * En caso de no existir, se retorna un puntero nulo.
 */
void *tablahash_buscar(TablaHash * tabla, void *clave, void *dato) {
  // Calculamos la posición de la clave dada, de acuerdo a la función hash.
  unsigned idx = tabla->hash(clave);
  idx = idx % tabla->capacidad;

  SNodo *temp = tabla->tabla[idx].datos;

  while (temp->dato != dato && temp->sig != NULL) {
    temp = temp->sig;
  }
  if (temp->dato != dato) {
    printf("El dato no se encuentra en la tabla\n");
  } else {
    return temp->dato;
  }
}

/**
 * Elimina un elemento de la tabla.
 */
void tablahash_eliminar(TablaHash * tabla, void *clave, void *dato) {
  // Calculamos la posición de la clave dada, de acuerdo a la función hash.
  unsigned idx = tabla->hash(clave);
  idx = idx % tabla->capacidad;

  if (tabla->tabla[idx].datos->sig == NULL
      && tabla->tabla[idx].datos->dato == dato) {
    tabla->tabla[idx].datos->dato = NULL;
    tabla->tabla[idx].clave = NULL;
  } else {
    if (tabla->tabla[idx].datos->dato == dato) {
      SList nodoAEliminar = tabla->tabla[idx].datos;
      tabla->tabla[idx].datos = tabla->tabla[idx].datos->sig;
      free(nodoAEliminar);
    }
    while (tabla->tabla[idx].datos->sig != NULL
           && tabla->tabla[idx].datos->sig->dato != dato) {
      tabla->tabla[idx].datos = tabla->tabla[idx].datos->sig;
    }
    if (tabla->tabla[idx].datos->sig == NULL) {
      return;
    } else {
      SList nodoAEliminar = tabla->tabla[idx].datos->sig;
      tabla->tabla[idx].datos->sig = tabla->tabla[idx].datos->sig->sig;
      free(nodoAEliminar);
    }
  }
}

/**
 * Destruye la tabla.
 */
void tablahash_destruir(TablaHash * tabla) {
  for (unsigned idx = 0; idx < tabla->capacidad; idx++) {
    SNodo *nodoAEliminar;
    while (tabla->tabla[idx].datos != NULL) {
      nodoAEliminar = tabla->tabla[idx].datos;
      tabla->tabla[idx].datos = tabla->tabla[idx].datos->sig;
      free(nodoAEliminar);
    }
  }
  free(tabla->tabla);
  free(tabla);
}
