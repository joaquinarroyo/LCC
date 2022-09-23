#include "persona.h"
#include "GList.h"
#include "input.h"
#include "output.h"
#include <stdio.h>
#include <time.h>
#include <string.h>
#include <locale.h>
#include <wchar.h>
#include <stdlib.h>

/*
El programa recibe un archivo de entrada el cual es generado por el programa
generador.c, 6 nombres de archivos de salida y dos atributos de la estructura
Persona, con los cuales se van a realizar las comparaciones.
El programa toma las personas del archivo de entrada y las vuelca a una lista
doblemente enlazada, en la cual cada nodo va a contener una estructura Persona.
Luego ordena dicha lista a traves de 3 algoritmos(selection sort, insertion sort
y merge sort) comparando las personas segun los dos atributos elegidos.
Escribe cada lista ordenada en un archivo de la forma:
Algoritmo usado, Atributo por el cual se comparo.
Tiempo en que tardo en ordenarse la lista.
Lista ordenada de la forma donde cada linea es de la forma
"nombre, edad, lugar".
*/

int comparar_nombre(void *dato1, void *dato2) {
  /*
     Recibe dos void pointers.
     Realiza un casteo para asi acceder a los datos de la estructura persona
     a la cual apunta cada puntero.
     Toma el nombre de cada persona y los compara.
     Si nombre de dato1 < nombre de dato 2 -> retorna un numero negativo
     Si nombre de dato1 > nombre de dato 2 -> retorna un numero positivo
     Si nombre de dato1 = nombre de dato 2 -> retorna 0
   */
  wchar_t *nombre1 = (*(Persona *) dato1).nombre;
  wchar_t *nombre2 = (*(Persona *) dato2).nombre;
  return comparador(nombre1, nombre2);
}

int comparar_edad(void *dato1, void *dato2) {
  /*
     Recibe dos void pointers.
     Realiza un casteo para asi acceder a los datos de la estructura persona
     a la cual apunta cada puntero.
     Toma la edad de cada persona y los compara.
     Si edad de dato1 < edad de dato 2 -> retorna -1
     Si edad de dato1 > edad de dato 2 -> retorna  1
     Si edad de dato1 = edad de dato 2 -> retorna  0
   */
  int edad1 = (*(Persona *) dato1).edad;
  int edad2 = (*(Persona *) dato2).edad;
  if (edad1 > edad2) {
    return 1;
  } else {
    if (edad1 == edad2) {
      return 0;
    } else {
      return -1;
    }
  }
}


void destruir_dato(void *dato) {
  /*
     Recibe un void pointer.
     Casteamos el void pointer como persona, para asi poder liberar la memoria
     pedida para los atributos de persona que son punteros.
     Libera el bloque donde apunta dato.
   */
  free((*(Persona *) dato).nombre);
  free((*(Persona *) dato).lugarDeNacimiento);
  free(dato);
}

void generar_archivo(FILE * fp, Algoritmo metodo, Compara c, GList lista) {
  /*
     Recibe un file pointer, una funcion de tipo Algoritmo, una funcion de tipo
     compara y el primer nodo de una lista.
     Genera una copia del primer nodo de la lista, ordena la lista con el 
     algoritmo segun la funcion compara y escribe en fp:
     El tiempo que tardo el algoritmo.
     Lista ordenada de la forma "nombre, edad, lugar".
   */
  GList listaOrdenada = lista;
  clock_t inicio = clock();
  listaOrdenada = metodo(listaOrdenada, c);
  clock_t final = clock();
  GList nodoAImprimir = listaOrdenada;
  double tiempo = (double) (final - inicio) / CLOCKS_PER_SEC;
  fwprintf(fp, L"Tiempo que tardo en ejecutarse el algoritmo: %f segundos\n\n",
           tiempo);
  for (; nodoAImprimir != NULL; nodoAImprimir = nodoAImprimir->sig) {
    fwprintf(fp, (*(Persona *) nodoAImprimir->dato).nombre);
    fwprintf(fp, L", ");
    fwprintf(fp, L"%d, ", (*(Persona *) nodoAImprimir->dato).edad);
    fwprintf(fp, (*(Persona *) nodoAImprimir->dato).lugarDeNacimiento);
    fwprintf(fp, L"\n");
  }
}

int main(int argc, char **argv) {
  setlocale(LC_ALL, "");
  FILE *entrada;
  entrada = fopen(argv[1], "r");        //Archivo de personas generadas por generador.c
  GList listaPersonas = glist_crear();
  listaPersonas = leer_archivo_personas(entrada, listaPersonas);

  FILE* salida1;
  salida1 = fopen(argv[2], "w+");
  fwprintf(salida1, L"Algoritmo: Selection Sort, Atributo: Nombre\n");
  generar_archivo(salida1, glist_selectionSort, comparar_nombre, listaPersonas);
  fclose(salida1);

  FILE* salida2;
  salida2 = fopen(argv[3], "w+");
  fwprintf(salida1, L"Algoritmo: Insertion Sort, Atributo: Nombre\n");
  generar_archivo(salida2, glist_insertionSort, comparar_nombre, listaPersonas);
  fclose(salida2);

  FILE* salida3;
  salida3 = fopen(argv[4], "w+");
  fwprintf(salida1, L"Algoritmo: Merge Sort, Atributo: Nombre\n");
  generar_archivo(salida3, glist_mergeSort, comparar_nombre, listaPersonas);
  fclose(salida3);

  FILE* salida4;
  salida4 = fopen(argv[5], "w+");
  fwprintf(salida1, L"Algoritmo: Selection Sort, Atributo: Edad\n");
  generar_archivo(salida4, glist_selectionSort, comparar_edad, listaPersonas);
  fclose(salida4);

  FILE* salida5;
  salida5 = fopen(argv[6], "w+");
  fwprintf(salida5, L"Algoritmo: Insertion Sort, Atributo: Edad\n");
  generar_archivo(salida5, glist_insertionSort, comparar_edad, listaPersonas);
  fclose(salida5);

  FILE* salida6;
  salida6 = fopen(argv[7], "w+");
  fwprintf(salida1, L"Algoritmo: Merge Sort, Atributo: Edad\n");
  generar_archivo(salida6, glist_mergeSort, comparar_edad, listaPersonas);
  fclose(salida6);

  glist_destruir(listaPersonas, destruir_dato);
}
