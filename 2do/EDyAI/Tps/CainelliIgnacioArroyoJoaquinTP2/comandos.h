#ifndef __COMANDOS_H__
#define __COMANDOS_H__
#include <ctype.h>
#include <string.h>
#include "itree.h"
#define MAX_CARAC 100

/**
 * Toma un arreglo de caracteres que representa al comando recibido por consola
 * y dependiendo dicho comando devuelve un entero.
 */ 
int opcion(char* comando);

 
/**
 * Toma un arreglo de caracteres y un entero i(index), y devuelve
 * la cantidad de caracteres que hay desde linea[i] hasta que se encuentra
 * con una , o un ]. 
 */ 
int cant_num(char* linea, int i);

 
/**
 * Toma un arreglo de caracteres el cual representa a un invervalo de la 
 * forma [double, double] y un intervalo, y pasa los datos del arreglo a 
 * la estructura intervalo.
 */ 
void consola_intervalo(char* linea, Interval intervalo);

 
/**
 * Toma un arreglo de caracteres que representa al comando recibido por
 * consola, y revisa si las variables del comando son validas.
 */ 
int variable_assert(char* comando);

 
/**
 * Toma un intervalo y revisa si el extIzq es menor o igual al
 * extDer.
 */ 
int interval_assert(Interval intervalo);

 
/**
 * Toma un nodo y si este es NULL, imprime No, en caso contrario
 * imprime Si, [extIzq, extDer], donde extIzq y extDer son los extremos
 * del intervalo del nodo.
 */ 
void verificar_interseccion(ITree nodo, FuncionVisitante visit);

 
#endif                          /* __COMANDOS_H__ */
