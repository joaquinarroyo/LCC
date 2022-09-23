#include "input.h"
#include "persona.h"
#include "GList.h"

int cantidad_lineas(FILE * fp) {
  int contador = 0;
  char carac = fgetwc(fp);
  while (carac != EOF) {
    if (carac == '\n') {
      contador++;
    }
    carac = fgetwc(fp);
  }
  rewind(fp);
  return contador;
}

void leer_archivo(FILE * fp, wchar_t * lista[]) {
  wchar_t buff[MAX];
  int contador = 0;
  while (fgetws(buff, MAX, (FILE *) fp)) {
    int i = 0, j = 0, n = wcslen(buff);
    lista[contador] = malloc(sizeof(size_t) * n);
    buff[n - 2] = 0;
    while (buff[i] != '\0') {
      lista[contador][j] = buff[i];
      i++;
      j++;
    }
    lista[contador][j] = '\0';
    contador++;
  }
}

GList leer_archivo_personas(FILE * fp, GList lista) {
  wchar_t buff[MAX];
  while (fgetws(buff, MAX, (FILE *) fp)) {
    int n = wcslen(buff);
    buff[n - 1] = 0;
    Persona *individuo = malloc(sizeof(Persona));
    linea_a_persona(buff, individuo);
    lista = glist_agregar_final(lista, individuo);
  }
  return lista;
}

void liberar_memoria(wchar_t * lista[], int lineas) {
  int contador = 0;
  while (contador < lineas) {
    free(lista[contador]);
    contador++;
  }
}

void liberar_persona(Persona person) {
  free(person.nombre);
  free(person.lugarDeNacimiento);
}
