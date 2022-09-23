#include "output.h"

void convertir_string(wchar_t * palabra) {
  int i = 1;
  while (palabra[i] != '\0') {
    if (palabra[i] == ' ') {
      i++;
    } else {
      if (palabra[i] == L'Ñ') {
        palabra[i] = L'ñ';
      } else {
        if (palabra[i] == L'Á') {
          palabra[i] = L'á';
        } else {
          if (palabra[i] == L'É') {
            palabra[i] = L'é';
          } else {
            if (palabra[i] == L'Í') {
              palabra[i] = L'í';
            } else {
              if (palabra[i] == L'Ó') {
                palabra[i] = L'ó';
              } else {
                if (palabra[i] == L'Ú') {
                  palabra[i] = L'ú';
                } else {
                  palabra[i] += 32;
                }
              }
            }
          }
        }
      }
    }
    i++;
  }
}



int comparador(wchar_t * palabra1, wchar_t * palabra2) {
  /*
  Se procede a comparar palabra1 y palabra2, colocando la letra ñ entre la letra n y o
  */
  int index = 0;
  int resultado = 0;
  while ((palabra1[index] != L'\0') && (palabra1[index] != L'\0')
         && (resultado == 0)) {
    if ((palabra1[index] != 241) && (palabra2[index] != 241)) {
      if (palabra1[index] < palabra2[index]) {
        resultado = -1;
      }
      if (palabra1[index] > palabra2[index]) {
        resultado = 1;
      }
    }
    if (palabra1[index] == 241) {
      if (palabra2[index] == 32) {
        resultado = -1;
      }
      if ((palabra2[index] > 110 && palabra2[index] < 123)
          || (palabra2[index] > 77 && palabra2[index] < 91)) {
        resultado = -1;
      }
      if ((palabra2[index] > 96 && palabra2[index] < 111)
          || (palabra2[index] > 64 && palabra2[index] < 78)) {
        resultado = 1;
      }
    }
    if (palabra2[index] == 241) {
      if (palabra1[index] == 32) {
        resultado = 1;
      }
      if ((palabra1[index] > 110 && palabra1[index] < 123)
          || (palabra1[index] > 77 && palabra1[index] < 91)) {
        resultado = 1;
      }
      if ((palabra1[index] > 96 && palabra1[index] < 111)
          || (palabra1[index] > 64 && palabra1[index] < 78)) {
        resultado = -1;
      }
    }

    index++;
  }
  if ((palabra1[index] == L'\0') && (resultado == 0)
      && (palabra2[index] != L'\0')) {
    resultado = -1;
  }
  if ((palabra2[index] == L'\0') && (resultado == 0)
      && (palabra1[index] != L'\0')) {
    resultado = 1;
  }

  return resultado;
}

void escribir_salida(FILE * fp, wchar_t * nombre, int edad, wchar_t * lugar) {
  fwprintf(fp, nombre);
  fwprintf(fp, L", ");
  fwprintf(fp, L"%d, ", edad);
  fwprintf(fp, lugar);
  fwprintf(fp, L"\n");
}
