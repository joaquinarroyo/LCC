#include "input.h"
#include "output.h"
#include "persona.h"
#include "GList.h"
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <locale.h>
#include <wchar.h>

/*
El programa recibe dos archivos de entrada, "personas.txt" y "paises.txt", 
un numero natural n(cantidad de personas a generar.), y un archivo de salida. 
Se representara a las personas como una estructura Persona que contiene:
Nombre y Apellido.
Edad.
Lugar de Nacimiento.
El programa vuelca la informacion de ambos archivos en dos listas de punteros, 
y, a partir de esa informacion, elije de manera aleatoria, n personas(diferentes),
n lugares y n edades(entre 1 y 100), para asi formar n personas, guardadas en un 
bloque de memoria anteriormente pedido.
Luego, pasa la informacion de cada una de las personas generadas al archivo de 
salida de la forma, "Nombre Apellido, edad, LugarDeNacimiento".
*/

int main(int argc, char **argv) {
  srand(time(NULL));
  setlocale(LC_ALL, "");

  FILE *entradaUno;
  entradaUno = fopen(argv[1], "r");     //Archivo de personas
  int cantidadLineasUno = cantidad_lineas(entradaUno);
  wchar_t *listaNombres[cantidadLineasUno];     //Lista con n nombres
  leer_archivo(entradaUno, listaNombres);
  fclose(entradaUno);

  FILE *entradaDos;
  entradaDos = fopen(argv[2], "r");     //Archivo de lugares
  int cantidadLineasDos = cantidad_lineas(entradaDos);
  wchar_t *listaLugares[cantidadLineasDos];     //Lista con n lugares
  leer_archivo(entradaDos, listaLugares);
  fclose(entradaDos);

  int cantidadDatos = atoi(argv[3]);
  Persona *listaFinal = malloc(sizeof(Persona) * cantidadDatos);        //Bloque que contendra a las personas

  generar_lista_final(listaFinal, cantidadDatos, listaNombres,
                      listaLugares, cantidadLineasUno, cantidadLineasDos);


  FILE *salida;
  salida = fopen(argv[4], "w+");        //Archivo de salida

  for (int i = 0; i < cantidadDatos; i++) {
    convertir_string(listaFinal[i].nombre);

    escribir_salida(salida, listaFinal[i].nombre, listaFinal[i].edad,
                    listaFinal[i].lugarDeNacimiento);

  }
  fclose(salida);

  liberar_memoria(listaNombres, cantidadLineasUno);
  liberar_memoria(listaLugares, cantidadLineasDos);
  for (int i = 0; i < cantidadDatos; i++) {
    liberar_persona(listaFinal[i]);
  }
  free(listaFinal);
}
