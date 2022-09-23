#include "persona.h"

int numero_aleatorio(int max) {
  /*
     Recibe un entero max.
     Devuelve un entero entre 0 y max.
   */
  int resultado;
  resultado = rand() % (max);
  return resultado;
}

int contador_caracteres(wchar_t * linea, int index) {
  /*
     Recibe un char pointer y un entero.
     Cuenta cuantos caracteres tiene linea, desde index, hasta que encuentra una 
     coma o un \0.
   */
  int contador = 0;
  while ((linea[index] != L',') && (linea[index] != L'\0')) {
    contador++;
    index++;
  }
  return contador;
}

void intercambiar_posicion(wchar_t * listaN[], int index, int cantN) {
  /*
     Recibe una lista de wchar punteros y dos enteros.
     Intercambia de posicion la persona que se encuentra en la posicion index con 
     la que se encuentra en la ultima.
   */
  wchar_t *tmp = malloc(sizeof(size_t) * (wcslen(listaN[index]) + 1));
  wcscpy(tmp, listaN[index]);
  listaN[index] = realloc(listaN[index], sizeof(size_t) *
                          (wcslen(listaN[cantN - 1]) + 1));
  wcscpy(listaN[index], listaN[cantN - 1]);
  listaN[cantN - 1] = realloc(listaN[cantN - 1], sizeof(size_t) *
                              (wcslen(tmp) + 1));
  wcscpy(listaN[cantN - 1], tmp);
}

Persona generar_persona(wchar_t * listaN[],
                        wchar_t * listaL[], int cantN, int cantL) {
  /*
     Recibe dos listas de wchar punteros y dos enteros.
     Pasa un dato de ambas listas y un entero(los tres aleatorios) a la estructura 
     persona, y retorna dicha estructura.
   */
  Persona person;
  int numeroIndexadoUno = numero_aleatorio(cantN);
  int numeroIndexadoDos = numero_aleatorio(cantL);
  person.nombre = malloc(sizeof(size_t) *
                         ((wcslen(listaN[numeroIndexadoUno])) + 1));
  wcscpy(person.nombre, listaN[numeroIndexadoUno]);
  person.edad = numero_aleatorio(MAXEDAD) + 1;
  person.lugarDeNacimiento = malloc(sizeof(size_t) *
                                    ((wcslen(listaL[numeroIndexadoDos])) + 1));
  wcscpy(person.lugarDeNacimiento, listaL[numeroIndexadoDos]);
  intercambiar_posicion(listaN, numeroIndexadoUno, cantN);
  return person;
}

void generar_lista_final(Persona * lista, int cantidad,
                         wchar_t * listaNombres[], wchar_t * listaLugares[],
                         int cantNombres, int cantLugares) {
  int contador = 0;
  int cantNombresTmp = cantNombres;
  while (contador < cantidad) {
    lista[contador] = generar_persona(listaNombres, listaLugares,
                                      cantNombresTmp, cantLugares);
    cantNombresTmp--;
    contador++;
  }
}

void linea_a_persona(wchar_t * linea, Persona * pers) {
  int cantCaracteresNombre, cantCaracteresEdad, cantCaracteresLugar;
  int contador = 0, index = 0;
  cantCaracteresNombre = contador_caracteres(linea, 0);
  cantCaracteresEdad = contador_caracteres(linea, cantCaracteresNombre + 1);
  cantCaracteresLugar =
      contador_caracteres(linea, cantCaracteresNombre + cantCaracteresEdad + 2);

  pers->nombre = malloc(sizeof(size_t) * cantCaracteresNombre);
  pers->lugarDeNacimiento = malloc(sizeof(size_t) * (cantCaracteresLugar));
  wchar_t *tmp = malloc(sizeof(size_t) * cantCaracteresEdad);

  index = 0;
  contador = 0;
  while (contador < cantCaracteresNombre) {
    pers->nombre[contador] = linea[index];
    index++;
    contador++;
  }
  pers->nombre[contador] = L'\0';
  contador = 0;
  index += 2;

  while (contador < cantCaracteresEdad) {
    tmp[contador] = linea[index];
    contador++;
    index++;
  }
  tmp[contador] = L'\0';

  char *tmp2 = malloc(sizeof(char) * (cantCaracteresEdad + 1));
  contador = 0;
  while (contador < cantCaracteresEdad) {
    tmp2[contador] = (char) tmp[contador];
    contador++;
  }
  tmp2[contador] = '\0';

  pers->edad = atoi(tmp2);
  free(tmp);
  free(tmp2);

  contador = 0;
  index += 1;
  while (contador < cantCaracteresLugar) {
    pers->lugarDeNacimiento[contador] = linea[index];
    index++;
    contador++;
  }
  pers->lugarDeNacimiento[contador] = L'\0';
}
