#include <stdio.h>
#include <stdlib.h>
#include "bstree.h"


static void imprimir_entero(int data) {
  printf("%d ", data);
}

int main() {
  BSTree raiz = bstree_crear();
  raiz = bstree_insertar(raiz, 6);
  raiz = bstree_insertar(raiz, 2);
  raiz = bstree_insertar(raiz, 1);
  raiz = bstree_insertar(raiz, 3);
  raiz = bstree_insertar(raiz, 7);
  raiz = bstree_insertar(raiz, 4);
  raiz = bstree_insertar(raiz, 5);
  raiz = bstree_insertar(raiz, 9);
  raiz = bstree_insertar(raiz, 3);
  bstree_eliminar(raiz, 5);
  printf("Cantidad elementos: %d\n", bstree_cant_elementos(raiz, 0));
  printf("Altura: %d\n", bstree_altura(raiz));
  printf("Minimo: %d\n", bstree_enterominimo(raiz));
  printf("Arbol(preorder): ");
  bstree_recorrer(raiz, BSTREE_RECORRIDO_PRE, imprimir_entero);
  printf("\n");
  printf("Arbol(inorder): ");
  bstree_recorrer(raiz, BSTREE_RECORRIDO_IN, imprimir_entero);
  printf("\n");
  printf("Arbol(postorder): ");
  bstree_recorrer(raiz, BSTREE_RECORRIDO_POST, imprimir_entero);
  printf("\n");
  bstree_destruir(raiz);
  
  return 0;
}
