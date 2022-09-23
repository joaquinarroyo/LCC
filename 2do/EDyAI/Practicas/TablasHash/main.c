#include <stdio.h>
#include <stdlib.h>
#include "tablahash.h"

unsigned hash(void* clave) {
  int* p = clave;
  return *p;
}

int main(void) {
  int x = 42, y = 40, z = 3, w = 7;
  TablaHash *th = tablahash_crear(10, hash);

  tablahash_insertar(th, &x, &z);
  tablahash_insertar(th, &y, &w);

  printf("z : %d\n", *((int *)tablahash_buscar(th, &x)));
  printf("z : %d\n", *((int *)tablahash_buscar(th, &y)));

  tablahash_eliminar(th, &x);

  tablahash_destruir(th);

  return 0;
}
