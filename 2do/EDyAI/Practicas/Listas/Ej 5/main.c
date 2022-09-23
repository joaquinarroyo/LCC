#include <stdlib.h>
#include <stdio.h>
#include "dlist.h"

static void imprimir_entero(int dato) {
  printf("%d ", dato);
}

int main(){
    DList* lista = dlist_crear();

    lista = dlist_agregar_inicio(lista, 3);
    lista = dlist_agregar_inicio(lista, 2);
    lista = dlist_agregar_inicio(lista, 1);
    lista = dlist_agregar_final(lista, 4);
    
    dlist_recorrer(lista,1,imprimir_entero);
    dlist_recorrer(lista,1,imprimir_entero);
    dlist_recorrer(lista,0,imprimir_entero);

    dlist_destruir(lista);
    
    return 0;
}