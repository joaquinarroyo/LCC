#ifndef __HEAPS_H__
#define __HEAPS_H__
#include <stdio.h>
#include <stdlib.h>
#define MAX_SIZE 80

typedef void (*FuncionVisitante) (int dato);

typedef struct _BHeap {
int datos[MAX_SIZE];
int nelems;
} *BHeap;

BHeap bheap_crear();

void bheap_destruir(BHeap heap);

int bheap_es_vacio(BHeap heap);

void bheap_insertar(BHeap heap, int dato);

void bheap_insertar_max(BHeap heap, int dato);

int bheap_nelementos(BHeap heap);

void bheap_recorrer(BHeap heap, FuncionVisitante visit);

int bheap_maximo(BHeap heap);

void bheap_eliminar_maximo(BHeap);

void heapify(int arr[], int n);

#endif /* __HEAPS_H__ */