#include "heaps.h"

void imprimir_dato(int dato){
  printf("%d ", dato);
}

int main(){
  BHeap heapMax = bheap_crear(); //heap1

  printf("%d\n", bheap_es_vacio(heapMax));
  bheap_insertar_max(heapMax, 4);
  bheap_insertar_max(heapMax, 2);
  bheap_insertar_max(heapMax, 3);
  bheap_insertar_max(heapMax, 1);
  bheap_insertar_max(heapMax, 5);
  bheap_insertar_max(heapMax, 2);
  bheap_eliminar_maximo(heapMax);
  printf("Heap1 cantidad de elementos: %d\n", bheap_nelementos(heapMax));
  printf("Heap1: ");
  bheap_recorrer(heapMax, imprimir_dato);
  printf("\n");
  printf("Maximo del heap1: %d\n", bheap_maximo(heapMax));
  bheap_destruir(heapMax);

  BHeap heap = bheap_crear(); //heap2
  bheap_insertar(heap, 2);  
  bheap_insertar(heap, 1);
  bheap_insertar(heap, 3);
  bheap_insertar(heap, 4);
  printf("Heap2 cantidad de elementos: %d\n", bheap_nelementos(heapMax));
  printf("Heap2: ");
  bheap_recorrer(heap, imprimir_dato);
  printf("\n");
  heapify(heap->datos, heap->nelems); //ordena el heap para que tenga la propiedad max_heap
  printf("Heap2(max_heap): ");
  bheap_recorrer(heap, imprimir_dato);
  printf("\n");
  printf("Maximo del heap2: %d\n", bheap_maximo(heap));
  bheap_destruir(heap);
}