#ifndef __ITREE_H__
#define __ITREE_H__
#include <stddef.h>
#include <stdlib.h>
#include <stdio.h>

/**
 * Estructura que representa al intervalo.
 */
typedef struct _Intervalo {
  double extIzq;
  double extDer;
} Intervalo;

typedef Intervalo *Interval;

/**
 * Estructura que representa a los nodos del arbol.
 */
typedef struct _INodo {
  struct _Intervalo *interval;
  double maxExtDer;
  struct _INodo *izq;
  struct _INodo *der;
  int altura;
} INodo;

typedef INodo *ITree;

typedef void (*FuncionVisitante) (ITree dato);

typedef void (*FuncionRecorrido) (ITree dato, FuncionVisitante visit);

/**
 * Inicializa un arbol.
 */
ITree itree_crear();

/**
 * Recibe un arbol y revisa si es vacio.
 */
int itree_es_vacio(ITree arbol);

/**
 * Recibe un arboly lo destruye
 */
void itree_destruir(ITree arbol);

/**
 * Recibe un arbol y un intervalo, e inserta dicho intervalo
 * en el arbol.
 */
ITree itree_insertar(ITree arbol, Interval segmento);

/**
 * Recibe un arbol y un intervalo, y elimina dicho intervalo
 * en el arbol.
 */
ITree itree_eliminar(ITree arbol, Interval segmento);

/**
 * Recibe un arbol y un intervalo, y devuelve un puntero
 * al nodo el cual contiene el intervalo con el cual el intervalo
 * recibido interseca. En caso de no encontrar retorna NULL.
 */
ITree itree_intersectar(ITree arbol, Interval segmento);

/**
 * Recorrido inorder.
 */
void itree_inorder(ITree arbol, FuncionVisitante visit);

/**
 * Recorre al arbol primero en profundidad, utilizando el recorrido
 * una funcion visitante para recorrer. En nuestro caso definimos
 * itree_inorder.
 */
void itree_recorrer_dfs(ITree arbol, FuncionRecorrido recorrido,
                        FuncionVisitante visit);

/**
 * Recorre al arbol primero a lo ancho.
 */
void itree_recorrer_bfs(ITree arbol, FuncionVisitante visit);

#endif                          /* __ITREE_H__ */
