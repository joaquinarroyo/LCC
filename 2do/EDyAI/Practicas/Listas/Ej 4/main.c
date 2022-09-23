#include <stdlib.h>
#include <stdio.h>
#include "slist.h"

static void imprimir_entero(int dato) {
  printf("%d ", dato);
}

int main(int argc, char *argv[]) {
  
  SList lista = slist_crear();
  
  lista = slist_agregar_inicio(lista, 3);
  lista = slist_agregar_inicio(lista, 2);
  lista = slist_agregar_inicio(lista, 1);
  lista = slist_agregar_final(lista, 4);

  slist_recorrer(lista, imprimir_entero);
  puts("");

  slist_destruir(lista);

  return 0;
}