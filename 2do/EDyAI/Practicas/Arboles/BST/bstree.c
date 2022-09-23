#include "bstree.h"
#include <stdlib.h>

BSTree bstree_crear() {
  return NULL;
}

void bstree_destruir(BSTree nodo) {
  if (nodo != NULL) {
    bstree_destruir(nodo->left);
    bstree_destruir(nodo->right);
    free(nodo);
  }
}

int bstree_empty(BSTree nodo) {
  return nodo == NULL;
}

BSTree bstree_insertar(BSTree arbol, int dato){
  if(bstree_empty(arbol)){
    arbol = malloc(sizeof(BSTNodo));
    arbol->left = NULL;
    arbol->right = NULL;
    arbol->dato = dato;
  }
  else if (arbol->dato > dato)
    arbol->left = bstree_insertar(arbol->left, dato);
  else if(arbol->dato < dato)
    arbol->right = bstree_insertar(arbol->right, dato);
  return arbol;
}

void bstree_eliminar_nodo(BSTree nodoAEliminar, int dato){
  if(nodoAEliminar->right && nodoAEliminar->left){
    BSTree menor = bstree_minimo(nodoAEliminar->right);
    nodoAEliminar->dato = menor->dato;
    bstree_eliminar_nodo(menor);
  }
}
  
void bstree_eliminar(BSTree arbol, int dato){
  BSTree padre = bstree_buscar_padre(arbol, dato);
  bstree_eliminar_nodo(padre, dato);
}

BSTree bstree_minimo(BSTree arbol){
  if(arbol == NULL){
    return NULL;
  }
  if(arbol->left){
    return bstree_minimo(arbol);
  }else{
    return arbol;
  }
}

BSTree bstree_buscar_padre(BSTree arbol, int dato){
  BSTree tmp = NULL;
  if(arbol == NULL){
    return NULL;
  }
  if(arbol->left != NULL){
    if(arbol->left->dato == dato){
      return arbol;
    }
  }
  if(arbol->right != NULL){
    if(arbol->right->dato == dato){
      return arbol;
    }
  }
  if(arbol->left != NULL && arbol->dato > dato){
    tmp = bstree_buscar_padre(arbol->left, dato);
  }
  if(arbol->right != NULL && arbol->dato < dato){
    tmp = bstree_buscar_padre(arbol->right, dato);
  }
  return tmp;
}

int bstree_contiene(BSTree arbol, int dato){
  if(arbol == NULL){
    return 0;
  }
  if(arbol->dato > dato){
    bstree_contiene(arbol->left, dato);
  }else{
    if(arbol->dato < dato){
      bstree_contiene(arbol->right, dato);
    }else{
      return 1;
    }
  }
}

int bstree_cant_elementos(BSTree arbol, int contador){
  if(arbol == NULL){
    return contador;
  }
  contador ++;
  bstree_cant_elementos(arbol->left, bstree_cant_elementos(arbol->right, contador));
}

int bstree_altura(BSTree arbol){
  int AltL, AltR;
  if(arbol == NULL){
    return -1;
  }else{
    AltL = bstree_altura(arbol->left);
    AltR = bstree_altura(arbol->right);
    if(AltL > AltR){
      return AltL+1;
    }else{
      return AltR+1;
    }
  }
}

void bstree_recorrer(BSTree arbol, BSTreeOrdenDeRecorrido orden, FuncionVisitante visit){
  if(orden == BSTREE_RECORRIDO_IN){
    bstree_inorder(arbol, visit);
  }else{
    if(orden == BSTREE_RECORRIDO_POST){
      bstree_postorder(arbol, visit);
    }else{
      if(orden == BSTREE_RECORRIDO_PRE){
        bstree_preorder(arbol, visit);
      }
    }
  }
}

void bstree_inorder(BSTree arbol, FuncionVisitante visit){
  if(arbol == NULL){
    return;
  }
  bstree_preorder(arbol->left, visit);
  visit(arbol->dato);
  bstree_preorder(arbol->right, visit);
}

void bstree_preorder(BSTree arbol, FuncionVisitante visit){
  if(arbol == NULL){
    return;
  }
  visit(arbol->dato);
  bstree_preorder(arbol->left, visit);
  bstree_preorder(arbol->right, visit);
}

void bstree_postorder(BSTree arbol, FuncionVisitante visit){
  if(arbol == NULL){
    return;
  }
  bstree_preorder(arbol->left, visit);
  bstree_preorder(arbol->right, visit);
  visit(arbol->dato);
}

int bstree_enterominimo(BSTree arbol){
  if(arbol->left == NULL){
    return arbol->dato;
  }
  bstree_enterominimo(arbol->left);
}