#ifndef __OUTPUT_H__
#define __OUTPUT_H__
#include <stdio.h>
#include <stdlib.h>
#include <locale.h>
#include <wchar.h>
#include <string.h>
#include "persona.h"

typedef void (*imprimirDatos) (FILE* fp, void* dato);

/*
  Recibe un wchar pointer.
  Toma la palabra recibida y cambia sus caracteres de mayuscula a minuscula, 
  excepto el primer caracter, y todo caracter que se encuentre despues 
  de un espacio.
*/
void convertir_string(wchar_t* nombre);

/*
Recibe dos wchar pointers.
Si palabra1 < palabra2 -> retorna un numero negativo
Si palabra1 > palabra2 -> retorna un numero positivo
Si palabra1 = palabra2 -> retorna 0
*/
int comparador(wchar_t* palabra1, wchar_t* palabra2);

/*
  Recibe un file pointer, dos wchar pointer y un entero.
  Toma los datos recibidos y los escribe en fp de la forma:
  "nombre, edad, lugar".
*/
void escribir_salida(FILE* fp, wchar_t* nombre, int edad, wchar_t* lugar);

#endif
