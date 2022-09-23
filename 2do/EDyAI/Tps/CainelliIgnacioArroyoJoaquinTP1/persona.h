#ifndef __PERSONA_H__
#define __PERSONA_H__
#include <wchar.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#define MAXEDAD 100

/*
Estructura que representa a las personas.
*/
typedef struct {
  wchar_t* nombre;
  int edad;
  wchar_t* lugarDeNacimiento;
} Persona;

/*
Recibe un puntero a persona, tres enteros y dos listas de wchar punteros.
Genera la lista doblemente enlazada que contiene a las personas.
*/
void generar_lista_final(Persona* lista, int cantidad, wchar_t* listaNombres[], 
wchar_t* listaLugares[], int cantNombres, int cantLugares);

/*
Recibe un wchar pointer.
Pasa la informacion de linea, la cual contiene la informacion de una persona,
a la forma de la estrucutra persona.
*/
void linea_a_persona(wchar_t* linea, Persona* pers);

#endif