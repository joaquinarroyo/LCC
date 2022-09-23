#ifndef __BSTREE_H__
#define __BSTREE_H__
#include <stdlib.h>
#include <stdio.h>

typedef void (*FuncionVisitante) (int dato);

typedef enum {
  BSTREE_RECORRIDO_IN,
  BSTREE_RECORRIDO_PRE,
  BSTREE_RECORRIDO_POST,
} BSTreeOrdenDeRecorrido;

typedef struct _BSTNodo {
  int dato;
  struct _BSTNodo *left;
  struct _BSTNodo *right;
} BSTNodo;

typedef BSTNodo *BSTree;

/**
 * Devuelve un arbol vacío.
 */
BSTree bstree_crear();

/**
 * Destruccion del árbol.
 */
void bstree_destruir(BSTree nodo);

/**
 * Indica si el árbol es vacío.
 */
int bstree_empty(BSTree nodo);

/**
 * Iserta un elemento en el Arbol binario de busqueda.
 */
BSTree bstree_insertar(BSTree arbol, int dato);

/**
 * Elimina un elemento del arbol.
 */
void bstree_eliminar(BSTree arbol, int dato);

/**
 * Recorre el arbol de alguna forma segun el orden recibido.
 */
void bstree_recorrer(BSTree arbol, BSTreeOrdenDeRecorrido orden, FuncionVisitante visit);

/**
 * Recorre e imprime al arbol de forma inorder.
*/
void bstree_inorder(BSTree arbol, FuncionVisitante visit);

/**
 * Recorre e imprime al arbol de forma preorder.
*/
void bstree_preorder(BSTree arbol, FuncionVisitante visit);

/**
 * Recorre e imprime al arbol de forma postorder.
*/
void bstree_postorder(BSTree arbol, FuncionVisitante visit);

/**
 * recibe un entero y si esta en el arbol, lo elimina.
 */
void bstree_eliminar(BSTree arbol, int dato);

/**
 * recibe un nodo y lo elimina.
 */
void eliminar_nodo(BSTree arbol, int dato);

/**
 * recibe un arbol y encuentra su nodo minimo.
 */
BSTree bstree_minimo(BSTree arbol);

/**
 * recibe un nodo y un dato y encuentra el padre del nodo el cual
 * contiene el dato
 */
BSTree bstree_buscar_padre(BSTree arbol, int dato);

/**
 * recibe un entero y se fija si esta en el arbol.
 */
int bstree_contiene(BSTree arbol, int dato);

/**
 * recibe un arbol y devuelve cuantos elementos tiene.
 */
int bstree_cant_elementos(BSTree arbol, int contador);

/**
 * recibe un arbol y devuelve su altura.
 */
int bstree_altura(BSTree arbol);

/**
 * recibe un arbol y devuelve su elemento minimo
 */
int bstree_enterominimo(BSTree arbol);

#endif /* __BSTREE_H__ */
