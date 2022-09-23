#ifndef __BTREE_H__
#define __BTREE_H__
#include <stdlib.h>
#include <stdio.h>

typedef void (*FuncionVisitante) (int dato);

typedef enum {
  BTREE_RECORRIDO_IN,
  BTREE_RECORRIDO_PRE,
  BTREE_RECORRIDO_POST,
} BTreeOrdenDeRecorrido;

typedef struct _BTNodo {
  int dato;
  struct _BTNodo *left;
  struct _BTNodo *right;
} BTNodo;

typedef BTNodo *BTree;

/**
 * Devuelve un arbol vacío.
 */
BTree btree_crear();

/**
 * Destruccion del árbol.
 */
void btree_destruir(BTree nodo);

/**
 * Indica si el árbol es vacío.
 */
int btree_empty(BTree nodo);

/**
 * Crea un nuevo arbol, con el dato dado en el nodo raiz, y los subarboles dados
 * a izquierda y derecha.
 */
BTree btree_unir(int dato, BTree left, BTree right);

/**
 * Recorrido del arbol, utilizando la funcion pasada.
 */
void btree_recorrer(BTree arbol, BTreeOrdenDeRecorrido orden, FuncionVisitante visit);

/**
 * Recorre e imprime al arbol de forma inorder.
*/
void btree_inorder(BTree arbol, FuncionVisitante visit);

/**
 * Recorre e imprime al arbol de forma preorder.
*/
void btree_preorder(BTree arbol, FuncionVisitante visit);

/**
 * Recorre e imprime al arbol de forma postorder.
*/
void btree_postorder(BTree arbol, FuncionVisitante visit);

void btree_levelorder(BTree arbol);

/**
 * Devuelve la suma de los datos del arbol de enteros.
*/
int btree_sumar(BTree arbol, int dato);

/**
 * Devuelve la cantidad de nodos del arbol(internos).
*/
int btree_cant_nodos(BTree arbol, int contador);

/**
 * Devuelve la altura del arbol.
*/
int btree_altura(BTree arbol);

BTree mirror(BTree arbol);
#endif /* __BTREE_H__ */
