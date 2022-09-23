#ifndef __CONJUNTOS_H__
#define __CONJUNTOS_H__
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stddef.h>
#include <string.h>
#include <limits.h>

/**
 * Enumerado de los casos del switch.
 */
typedef enum {
  CREAR_EXT,
  CREAR_COMP,
  CREAR_VACIO,
  UNION,
  INTERSECCION,
  RESTA,
  COMPLEMENTO,
  IMPRIMIR,
  SALIR,
  INVALIDO,
} OpcionesMenu;

/**
 * Enumerado de los tipos de datos que pueden contener los nodos de la 
 * lista que representa al conjunto.
 */
typedef enum {
  NUMERO,
  INTERVALO,
  VACIO,
} TiposConjuntos;

/**
 * Estructura que representa a un intervalo.
 */
typedef struct _Interval{
  int extIzq;
  int extDer;
} Interval;

typedef Interval* Intervalo;

/**
 * Estructura de lista enlazada que representa a los conjuntos.
 */
typedef struct _CNodo{
  void* dato;
  int tipo;
  struct _CNodo *sig;
} CNodo;

typedef CNodo* CList;

/**
 * Estructura de lista enlazada que representa al area de rebalse.
 */
typedef struct _SNodo {
  char* alias;
  CList conjunto;
  struct _SNodo *sig;
  struct _CNodo *ultimo;
} SNodo;

typedef SNodo* SList;

/**
 * Estructura que representa a las casillas de la Tabla Hash.
 */
typedef struct {
  SList conjuntos;
} CasillaConjunto;

//Tipo de funcion Hash.
typedef unsigned (*FuncionHash)(void* clave);

/**
 * Estructura que representa a la Tabla Hash.
 */
typedef struct {
  CasillaConjunto* tabla;
  unsigned capacidad;
  FuncionHash hash;
} TablaConjuntos;

//Tipo de funcion que se utiliza para imprimir los conjuntos.
typedef void (*FuncionVisitante) (CList lista);

/**
 * Recibe la capacidad de la tabla y la funcion Hash e inicializa 
 * la Tabla Hash.
 */
TablaConjuntos* tablaconj_crear(unsigned capacidad, FuncionHash hash);

/**
 * Recibe la Tabla Hash, la clave, el dato que representa al nodo
 * en el cual esta el conjunto y su alias, e inserta dicho dato en
 * la tabla.
 */
void tablaconj_insertar(TablaConjuntos* tabla, void* clave, SList dato);

/**
 * Recibe la Tabla Hash, la clave, el alias y devuelve el nodo en el
 * cual esta la lista la cual esta relacionada con la clave y el alias 
 * recibidos.
 * En caso de que no haya ningun conjunto relacionado con dichos elementos, 
 * retornara NULL.
 */
SList tablaconj_buscar(TablaConjuntos* tabla, void* clave, char* alias);

/**
 * Recibe dos conjuntos, calcula su union y la retorna.
 */
SList tablaconj_union(SList conjB, SList conjC);

/**
 * Recibe dos conjuntos, calcula su interseccion y la retorna.
 */
SList tablaconj_interseccion(SList conjB, SList conjC);

/**
 * Recibe dos conjuntos, calcula su resta(conjB - conjC) y la retorna.
 * ConjB - ConjC = ConjB ∩ complemento(conjC).
 */
SList tablaconj_resta(SList conjB, SList conjC);

/**
 * Recibe un conjuntos, calcula su complemento y lo retorna.
 */
SList tablaconj_compl(SList conjuntoA);

/**
 * Recibe la Tabla Hash, una clave, un alias y una funcion de tipo 
 * FuncionVisitante e imprime el conjunto relacionado con la clave 
 * y el alias recibidos.
 */
void tablaconj_imprimir(TablaConjuntos* tabla, void* clave, char* alias, 
                            FuncionVisitante visit);

/**
 * Recibe la Tabla Hash y la destruye.
 */
void tablaconj_destruir(TablaConjuntos* tabla);

/**
 * Recibe dos conjuntos y revisa que no sean nulos.
 */
int conjuntos_assert(SList conjB, SList conjC, char *aliasB, char *aliasC);

/**
 * Recibe un nodo en el cual se encuentra el conjunto, un arreglo de 
 * enteros e inserta los enteros en el conjunto. En caso de que el 
 * tipo sea VACIO, va a insertar un nodo con dato NULL y tipo VACIO 
 * en el conjunto.
 */
SList conj_lista(SList lista, int dato[], int tipo, int cantidad);

/**
 * Algoritmo insertion sort.
 */
void insertion_sort(int conjunto[], int cantidad);

/**
 * Algoritmo para eliminar elementos duplicados del conjunto.
 */
int eliminar_dupl(int conjunto[],int cantidad);

#endif /* __CONJUNTOS_H__ */
