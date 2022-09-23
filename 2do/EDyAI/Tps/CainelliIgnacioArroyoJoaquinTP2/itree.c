#include "itree.h"

/**
 * Recibe un arbol y devuelve su altura.
 */
int itree_altura(ITree arbol) {
  if (itree_es_vacio(arbol)) {
    return 0;
  }
  return arbol->altura;
}

/**
 * Recibe un arbol y devuelve su balance.
 */
int itree_balance(ITree arbol) {
  if (itree_es_vacio(arbol)) {
    return 0;
  }
  return itree_altura(arbol->izq) - itree_altura(arbol->der);
}

/**
 * Recibe dos intervalos y verifica que intersequen.
 */
int intersectar(Interval a, Interval b) {
  if (a->extDer < b->extIzq || b->extDer < a->extIzq) {
    return 0;
  } else {
    return 1;
  }
}

/**
 * Recibe dos enteros a y b, y retorna el mayor entre ambos.
 */
double maximo(double a, double b) {
  if (a >= b) {
    return a;
  } else {
    return b;
  }
}

/**
 * Toma un nodo y actualiza su maximo extremo derecho.
 */
void actualizar_max(ITree nodo) {
  if (itree_es_vacio(nodo->izq) && itree_es_vacio(nodo->der)) {
    nodo->maxExtDer = nodo->interval->extDer;
  } else if (itree_es_vacio(nodo->izq)) {
    nodo->maxExtDer = maximo(nodo->der->interval->extDer,
                             nodo->interval->extDer);
  } else if (itree_es_vacio(nodo->der)) {
    nodo->maxExtDer = maximo(nodo->izq->interval->extDer,
                             nodo->interval->extDer);
  } else {
    nodo->maxExtDer = maximo(maximo(nodo->interval->extDer,
                                    nodo->izq->maxExtDer),
                             nodo->der->maxExtDer);
  }
}

/**
 * Recibe un arbol y devuelve su nodo mas a la izquierda.
 */
ITree nodo_valor_minimo(ITree arbol) {
  ITree s = arbol;
  while (s->izq != NULL) {
    s = s->izq;
  }
  return s;
}

/**
 * Recibe un arbol y un entero, e imprime los intervalos del arbol por nivel.
 */
void recorrer_niveles(ITree arbol, int nivel, FuncionVisitante visit) {
  if (itree_es_vacio(arbol)) {
    return;
  }
  if (nivel == 1) {
    visit(arbol);
  } else if (nivel > 1) {
    recorrer_niveles(arbol->izq, nivel - 1, visit);
    recorrer_niveles(arbol->der, nivel - 1, visit);
  }
}

/**
 * Rotacion a derecha del arbol.
 */
ITree rotacion_derecha(ITree C) {
  ITree B = C->izq;
  ITree hijoDerB = B->der;

  B->der = C;
  C->izq = hijoDerB;

  C->altura = maximo(itree_altura(C->izq), itree_altura(C->der)) + 1;
  B->altura = maximo(itree_altura(B->izq), itree_altura(B->der)) + 1;

  if (C->izq == NULL)
    C->maxExtDer = C->interval->extDer;
  else
    C->maxExtDer = maximo(C->interval->extDer, C->izq->interval->extDer);

  return B;
}

/**
 * Rotacion a izquierda del arbol.
 */
ITree rotacion_izquierda(ITree A) {
  ITree B = A->der;
  ITree hijoIzqB = B->izq;

  B->izq = A;
  A->der = hijoIzqB;

  A->altura = maximo(itree_altura(A->izq), itree_altura(A->der)) + 1;
  B->altura = maximo(itree_altura(B->izq), itree_altura(B->der)) + 1;

  if (A->der == NULL)
    A->maxExtDer = A->interval->extDer;
  else
    A->maxExtDer = maximo(A->interval->extDer, A->der->interval->extDer);

  return B;
}

ITree itree_crear() {
  return NULL;
}

int itree_es_vacio(ITree arbol) {
  return arbol == NULL;
}

void itree_destruir(ITree arbol) {
  if (!itree_es_vacio(arbol)) {
    itree_destruir(arbol->izq);
    itree_destruir(arbol->der);
    free(arbol->interval);
    free(arbol);
  }
}

ITree itree_insertar(ITree arbol, Interval segmento) {
  if (itree_es_vacio(arbol)) {
    arbol = malloc(sizeof(INodo));
    arbol->izq = NULL;
    arbol->der = NULL;
    arbol->interval = segmento;
    arbol->altura = 1;
    arbol->maxExtDer = segmento->extDer;
  } else if (segmento->extIzq < arbol->interval->extIzq) {
    arbol->izq = itree_insertar(arbol->izq, segmento);
  } else if (segmento->extIzq > arbol->interval->extIzq) {
    arbol->der = itree_insertar(arbol->der, segmento);
  } else if (segmento->extDer < arbol->interval->extDer) {
    arbol->izq = itree_insertar(arbol->izq, segmento);
  } else if (segmento->extDer > arbol->interval->extDer) {
    arbol->der = itree_insertar(arbol->der, segmento);
  } else {
    printf("No se permiten intervalos repetidos\n");
    return arbol;
  }

  arbol->altura = 1 + maximo(itree_altura(arbol->izq),
                             itree_altura(arbol->der));
  int balance = itree_balance(arbol);

  if (balance > 1
      && (segmento->extIzq < arbol->izq->interval->extIzq
          || segmento->extDer < arbol->izq->interval->extDer)) {
    return rotacion_derecha(arbol);
  }
  if (balance < -1
      && (segmento->extIzq > arbol->der->interval->extIzq
          || segmento->extDer < arbol->der->interval->extDer)) {
    return rotacion_izquierda(arbol);
  }

  if (balance > 1
      && (segmento->extIzq > arbol->izq->interval->extIzq
          || segmento->extDer < arbol->izq->interval->extDer)) {
    arbol->izq = rotacion_izquierda(arbol->izq);
    return rotacion_derecha(arbol);
  }
  if (balance < -1
      && (segmento->extIzq < arbol->der->interval->extIzq
          || segmento->extDer < arbol->der->interval->extDer)) {
    arbol->der = rotacion_derecha(arbol->der);
    return rotacion_izquierda(arbol);
  }
  actualizar_max(arbol);
  return arbol;
}

ITree itree_eliminar(ITree arbol, Interval segmento) {
  if (itree_es_vacio(arbol)) {
    printf("El intervalo no se encuentra en el arbol\n");
    return arbol;
  } else if (segmento->extIzq < arbol->interval->extIzq) {
    arbol->izq = itree_eliminar(arbol->izq, segmento);
  } else if (segmento->extIzq > arbol->interval->extIzq) {
    arbol->der = itree_eliminar(arbol->der, segmento);
  } else if (segmento->extDer < arbol->interval->extDer) {
    arbol->izq = itree_eliminar(arbol->izq, segmento);
  } else if (segmento->extDer > arbol->interval->extDer) {
    arbol->der = itree_eliminar(arbol->der, segmento);
  } else {
    if (itree_es_vacio(arbol->izq) || itree_es_vacio(arbol->der)) {
      ITree temp = arbol->izq ? arbol->izq : arbol->der;
      if (itree_es_vacio(temp)) {
        temp = arbol;
        arbol = NULL;
      } else {
        free(arbol->interval);
        *arbol = *temp;
      }
      free(temp);
    } else {
      ITree temp = nodo_valor_minimo(arbol->der);
      *(arbol->interval) = *(temp->interval);
      arbol->der = itree_eliminar(arbol->der, temp->interval);
    }
  }
  if (itree_es_vacio(arbol)) {
    return arbol;
  }

  actualizar_max(arbol);

  arbol->altura =
      maximo(itree_altura(arbol->izq), itree_altura(arbol->der)) + 1;
  int balance = itree_balance(arbol);

  if (balance > 1 && itree_balance(arbol->izq) >= 0) {
    return rotacion_derecha(arbol);
  }
  if (balance > 1 && itree_balance(arbol->izq) < 0) {
    arbol->izq = rotacion_izquierda(arbol->izq);
    return rotacion_derecha(arbol);
  }
  if (balance < -1 && itree_balance(arbol->der) <= 0) {
    return rotacion_izquierda(arbol);
  }
  if (balance < -1 && itree_balance(arbol->der) > 0) {
    arbol->der = rotacion_derecha(arbol->der);
    return rotacion_izquierda(arbol);
  }
  return arbol;
}

ITree itree_intersectar(ITree arbol, Interval segmento) {
  if (itree_es_vacio(arbol)) {
    return arbol;
  }
  if (intersectar(arbol->interval, segmento)) {
    return arbol;
  } else if (arbol->izq != NULL && arbol->izq->maxExtDer >= segmento->extIzq) {
    return itree_intersectar(arbol->izq, segmento);
  } else {
    return itree_intersectar(arbol->der, segmento);
  }
}

void itree_inorder(ITree arbol, FuncionVisitante visit) {
  ITree s = arbol;
  if (itree_es_vacio(arbol)) {
    return;
  }
  ITree l = s->izq;
  itree_inorder(l, visit);
  visit(s);
  ITree r = s->der;
  itree_inorder(r, visit);
}

void itree_recorrer_dfs(ITree arbol, FuncionRecorrido recorrer,
                        FuncionVisitante visit) {
  if (itree_es_vacio(arbol)) {
    printf("Arbol vacio");
    return;
  }
  recorrer(arbol, visit);
}

void itree_recorrer_bfs(ITree arbol, FuncionVisitante visit) {
  if (itree_es_vacio(arbol)) {
    printf("Arbol vacio");
    return;
  }
  int h = itree_altura(arbol);
  for (int i = 1; i <= h; i++) {
    recorrer_niveles(arbol, i, visit);
  }
}
