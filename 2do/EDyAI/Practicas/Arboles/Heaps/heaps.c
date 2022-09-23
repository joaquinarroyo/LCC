#include "heaps.h"

BHeap bheap_crear(){
  BHeap nuevoHeap = malloc(sizeof(BHeap));
  nuevoHeap->nelems = 0;
  return nuevoHeap;
}

void bheap_destruir(BHeap heap){
  free(heap);
}

int bheap_es_vacio(BHeap heap){
  return heap->nelems == 0;
}

void bheap_insertar(BHeap heap, int dato){
  heap->nelems++;
  heap->datos[heap->nelems] = dato;
}

void bheap_insertar_max(BHeap heap, int dato){
  int n = heap->nelems;
  heap->datos[++n] = dato;
for(int j = n; j > 1 && heap->datos[j] > heap->datos[j/2]; j/=2){
  int temp = heap->datos[j];
  heap->datos[j] = heap->datos[j/2];
  heap->datos[j/2] = temp;
  }
  heap->nelems ++;
}

int bheap_nelementos(BHeap heap){
  return heap->nelems;
}

void bheap_recorrer(BHeap heap, FuncionVisitante visit){
  for(int i = 1; i <= heap->nelems; i++){
      visit(heap->datos[i]);
  }
}

int bheap_maximo(BHeap heap){
  return heap->datos[1];
}

void bheap_eliminar_maximo(BHeap heap){
  int esMayor = 1, max = heap->datos[1], j = 1;
  heap->datos[1] = heap->datos[heap->nelems];
  while(2*j<= heap->nelems && esMayor){
    int k = 2*j;
    if(k+1 <= heap->nelems && heap->datos[k+1] > heap->datos[k]){
      k = k+1;
    }
    if(heap->datos[j] > heap->datos[k]){
      esMayor = 0;
    }else{
      int temp = heap->datos[j];
      heap->datos[j] = heap->datos[k];
      heap->datos[k] = temp;
      j = k;
    }
  }
  heap->nelems --;
}

void heapify(int arr[], int n){
  for(int i = 1; i < n ; i++){
    for(int j = i + 1 ; j <= n ; j++){
      if(arr[i] < arr[j]){
        int temp = arr[i];
        arr[i] = arr[j];
        arr[j] = temp;
      }
    }     
  }
}
