#ifndef __INPUT_H__
#define __INPUT_H__
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <wchar.h>
#include "persona.h"
#include "GList.h"
#define MAX 80

/*
Recibe un file pointer y devuelve la 
cantidad de lineas del archivo donde apunta fp.
*/
int cantidad_lineas(FILE* fp);

/*
Recibe un file pointer, una lista de punteros, 
y pasa toda la informacion del archivo
donde apunta fp a la lista.
*/
void leer_archivo(FILE* fp, wchar_t* lista[]);

/*
Recibe una lista de punteros, y un entero que representa a la 
cantidad de elementos de la lista y libera la 
memoria de cada puntero de la lista.
*/
GList leer_archivo_personas(FILE* fp, GList lista);

/*
Recibe un file pointer, y el primer nodo de una lista 
doblemente enlazada, y pasa la informacion
del archivo donde apunta fp a la lista.
*/
void liberar_memoria(wchar_t* lista[], int lineas);

/*
Recibe una Persona.
Libera la memoria de los punteros en Persona.
*/
void liberar_persona(Persona person);

#endif