#include <stdio.h>
#include <stdlib.h>
#include "tablahash.h"

int iguales(void* clave1, void* clave2) {
  int* p = clave1;
  int* q = clave2;
  return *p == *q;
}

unsigned hash(void* clave) {
  int* p = clave;
  return *p;
}

int main(void) {
  int x = 42, y = 42, z = 3, w = 1;
  TablaHash* th = tablahash_crear(10, hash);
  
  tablahash_insertar(th, &x, &z);
  tablahash_insertar(th, &y, &w);

  printf("z : %d\n", *((int *)tablahash_buscar(th, &x, &z)));
  printf("w : %d\n", *((int *)tablahash_buscar(th, &y, &w)));

  tablahash_eliminar(th, &x, &z);

  printf("w : %d\n", *((int *)tablahash_buscar(th, &y, &z)));
  
  tablahash_destruir(th);

  return 0;
}
