#include "btree.h"
#include <stdlib.h>

BTree btree_crear() {
  return NULL;
}

void btree_destruir(BTree nodo) {
  if (nodo != NULL) {
    btree_destruir(nodo->left);
    btree_destruir(nodo->right);
    free(nodo);
  }
}

int btree_empty(BTree nodo) {
  return nodo == NULL;
}

BTree btree_unir(int dato, BTree left, BTree right) {
  BTree nuevoNodo = malloc(sizeof(BTNodo));
  nuevoNodo->dato = dato;
  nuevoNodo->left = left;
  nuevoNodo->right = right;
  return nuevoNodo;
}

void btree_recorrer(BTree arbol, BTreeOrdenDeRecorrido orden, FuncionVisitante visit){
  if(orden == BTREE_RECORRIDO_IN){
    btree_inorder(arbol, visit);
  }else{
    if(orden == BTREE_RECORRIDO_POST){
      btree_postorder(arbol, visit);
    }else{
      if(orden == BTREE_RECORRIDO_PRE){
        btree_preorder(arbol, visit);
      }
    }
  }
}

void btree_inorder(BTree arbol, FuncionVisitante visit){
  if(arbol == NULL){
    return;
  }
  btree_preorder(arbol->left, visit);
  visit(arbol->dato);
  btree_preorder(arbol->right, visit);
}

void btree_preorder(BTree arbol, FuncionVisitante visit){
  if(arbol == NULL){
    return;
  }
  visit(arbol->dato);
  btree_preorder(arbol->left, visit);
  btree_preorder(arbol->right, visit);
}

void btree_postorder(BTree arbol, FuncionVisitante visit){
  if(arbol == NULL){
    return;
  }
  btree_preorder(arbol->left, visit);
  btree_preorder(arbol->right, visit);
  visit(arbol->dato);
}

int btree_sumar(BTree arbol, int dato){
  if(arbol == NULL){
    return dato;
  }
  if(arbol->right != NULL){
    dato += arbol->right->dato;;
  }
  if(arbol->left != NULL){
    dato += arbol->left->dato;;
  }

  btree_sumar(arbol->left, btree_sumar(arbol->right, dato));
}

int btree_cant_nodos(BTree arbol, int contador){
  if(arbol == NULL){
    return contador;
  }
  contador ++;
  btree_cant_nodos(arbol->left, btree_cant_nodos(arbol->right, contador));
}

int btree_altura(BTree arbol){
  int AltL, AltR;
  if(arbol == NULL){
    return -1;
  }else{
    AltL = btree_altura(arbol->left);
    AltR = btree_altura(arbol->right);
    if(AltL > AltR){
      return AltL+1;
    }else{
      return AltR+1;
    }
  }
}

void imprimir_niveles(BTree arbol, int nivel){
  if(arbol == NULL){
    return; 
  }
  if(nivel == 1){
    printf("%d ", arbol->dato); 
  }else{
    if(nivel > 1){
      imprimir_niveles(arbol->left, nivel-1); 
      imprimir_niveles(arbol->right, nivel-1); 
    }
  } 
} 

void btree_levelorder(BTree arbol){
  int h = btree_altura(arbol);
  for(int i = 1; i <= h+1; i++){
    imprimir_niveles(arbol, i);
  }
}

BTree mirror(BTree arbol){
  BTree tmp;
  if(arbol != NULL){
    tmp = arbol->left;
    arbol->left = mirror(arbol->right);
    arbol->right = mirror(tmp);
  }
  return arbol;
}