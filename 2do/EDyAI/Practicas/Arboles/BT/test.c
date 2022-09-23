#include <stdio.h>
#include <stdlib.h>
#include "btree.h"


static void imprimir_entero(int data) {
  printf("%d ", data);
}


int main() {
  BTree ll = btree_unir(1, btree_crear(), btree_crear());
  BTree l = btree_unir(2, ll, btree_crear());
  BTree rl = btree_unir(5, btree_crear(), btree_crear());
  BTree rr = btree_unir(7, btree_crear(), btree_crear());
  BTree r = btree_unir(3, rl, rr);
  BTree raiz = btree_unir(4, l, r);

  printf("Arbol(preorder): ");
  btree_recorrer(raiz, BTREE_RECORRIDO_PRE, imprimir_entero);
  printf("\n");
  printf("Arbol(inorder): ");
  btree_recorrer(raiz, BTREE_RECORRIDO_IN, imprimir_entero);
  printf("\n");
  printf("Arbol(postorder): ");
  btree_recorrer(raiz, BTREE_RECORRIDO_POST, imprimir_entero);
  printf("\n");

  printf("Suma de los datos del arbol de enteros: %d\n", btree_sumar(raiz, raiz->dato));
  printf("Cantidad de nodos del arbol(internos): %d\n", btree_cant_nodos(raiz, 0));
  printf("Altura del arbol: %d\n", btree_altura(raiz));
  
  printf("Arbol por niveles: ");
  btree_levelorder(raiz);
  printf("\n");

  BTree raizEspejo = NULL;
  raizEspejo = mirror(raiz);

  printf("ArbolEspejo(preorder): ");
  btree_recorrer(raizEspejo, BTREE_RECORRIDO_PRE, imprimir_entero);
  printf("\n");
  printf("ArbolEspejo(inorder): ");
  btree_recorrer(raizEspejo, BTREE_RECORRIDO_IN, imprimir_entero);
  printf("\n");
  printf("ArbolEspejo(postorder): ");
  btree_recorrer(raizEspejo, BTREE_RECORRIDO_POST, imprimir_entero);
  printf("\n");

  btree_destruir(raiz);
  
  return 0;
}
