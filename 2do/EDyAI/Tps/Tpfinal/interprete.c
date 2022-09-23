#include "conjuntos.h"
#include "comandos.h"
#define MAX_CARAC 500

/**
 * Recibe el alias del conjunto y devuelve su clave.
 */
int conseguir_clave(char* alias) {
  int clave = 0;
  for(int i = 0; alias[i] != '\0'; i++){
    clave += 3*alias[i];
  }
  return clave;
}

/**
 * Funcion hash
 */
unsigned hash(void *clave) {
  int *idx = clave;
  return *idx;
}

/**
 * Funcion de tipo FuncionVisitante que imprime el conjunto recibido.
 */
void imprimir_conjunto(CList conjunto) {
  CList nodo = conjunto;
  while (nodo->sig != NULL) {
    if (nodo->tipo == INTERVALO) {
      Interval intervalo = *((Interval *)(nodo->dato));
      printf("%d:%d,", intervalo.extIzq, intervalo.extDer);
    } else {
        int dato = *((int *)nodo->dato);
        printf("%d,", dato);
    }
    nodo = nodo->sig;
  }
  if (nodo->tipo == INTERVALO) {
    Interval intervalo = *((Interval *)(nodo->dato));
    printf("%d:%d\n", intervalo.extIzq, intervalo.extDer);
  } else {
      int dato = *((int *)nodo->dato);
      printf("%d\n", dato);
  }
}

/**
 * Menu del interprete.
 */
void menu(TablaConjuntos* tabla) {
  int opc;
  do {
    char comando[MAX_CARAC];
    scanf(" %500[^\n]", comando);
    opc = opcion(comando);
    SList lista = NULL;
    int clave;
    char *alias;

    if (opc != SALIR && opc != INVALIDO) {
      alias = comando_alias(comando);
      clave = conseguir_clave(alias);
    }

    switch(opc) {

      case CREAR_EXT:
        if (extension_assert(comando)) {
          int size = cantidad_elementos(comando);
          int conjunto[size];
          comando_conjunto(comando, conjunto, CREAR_EXT, size);
          size = eliminar_dupl(conjunto, size);
          insertion_sort(conjunto, size);
          lista = conj_lista(lista, conjunto, NUMERO, size);
          lista->alias = alias;
          tablaconj_insertar(tabla, &clave, lista);
        } else {
            printf("    ");
            printf("Los conjuntos por extension se ingresan de la " 
                    "siguiente manera:\n");
            printf("    ");
            printf("alias = {n,...,m} donde n y m son enteros\n");
            free(alias);
        }
        break;

      case CREAR_COMP:
        if (compresion_assert(comando)) {
          int conjunto[2]; 
          comando_conjunto(comando, conjunto, CREAR_COMP, 0);
          if (conjunto[0] == conjunto[1]) {
            lista = conj_lista(lista, &conjunto[0], NUMERO, 1);
            lista->alias = alias;
            tablaconj_insertar(tabla, &clave, lista);
          } else {
              lista = conj_lista(lista, conjunto, INTERVALO, 0);
              lista->alias = alias;
              tablaconj_insertar(tabla, &clave, lista);
          }
        } else {
            printf("    ");
            printf("Los conjuntos por compresion se ingresan de la "
                    "siguiente manera:\n");
            printf("    ");
            printf("alias = {x : n <= x <= m} donde n y m son enteros\n");
            free(alias);
        }
        break;

      case CREAR_VACIO:
        lista = conj_lista(lista, 0, VACIO, 0);
        lista->alias = alias;
        tablaconj_insertar(tabla, &clave, lista);
        break;

      case UNION:
        if (operaciones_dos_conj_assert(comando)) {
          char *aliasByC[2];
          comando_aliasbyc(comando, aliasByC);
          char *aliasB = aliasByC[0];
          char *aliasC = aliasByC[1];
          int claveB = conseguir_clave(aliasB);
          int claveC = conseguir_clave(aliasC);
          SList conjB = tablaconj_buscar(tabla, &claveB, aliasB);
          SList conjC = tablaconj_buscar(tabla, &claveC, aliasC);
          if (conjuntos_assert(conjB, conjC, aliasB, aliasC)) {
            lista = tablaconj_union(conjB, conjC);
            lista->alias = alias;
            tablaconj_insertar(tabla, &clave, lista);
          } else {
              free(alias);
          }
        } else {
            printf("    ");
            printf("La operacion union se ingresa de la siguiente manera:\n");
            printf("    ");
            printf("alias1 = alias2 | alias3\n");
            free(alias);
        }
        break;

      case INTERSECCION:
        if (operaciones_dos_conj_assert(comando)) {
          char *aliasByC[2];
          comando_aliasbyc(comando, aliasByC);
          char *aliasB = aliasByC[0];
          char *aliasC = aliasByC[1];
          int claveB = conseguir_clave(aliasB);
          int claveC = conseguir_clave(aliasC);
          SList conjB = tablaconj_buscar(tabla, &claveB, aliasB);
          SList conjC = tablaconj_buscar(tabla, &claveC, aliasC);
          if (conjuntos_assert(conjB, conjC, aliasB, aliasC)) {
            lista = tablaconj_interseccion(conjB, conjC);
            lista->alias = alias;
            tablaconj_insertar(tabla, &clave, lista);
          } else {
              free(alias);
          }
        } else {
            printf("    ");
            printf("La operacion interseccion se ingresa de la "
                    "siguiente manera:\n");
            printf("    ");
            printf("alias1 = alias2 & alias3\n");
            free(alias);
        }
        break;

      case RESTA:
        if (operaciones_dos_conj_assert(comando)) {
          char *aliasByC[2];
          comando_aliasbyc(comando, aliasByC);
          char *aliasB = aliasByC[0];
          char *aliasC = aliasByC[1];
          int claveB = conseguir_clave(aliasB);
          int claveC = conseguir_clave(aliasC);
          SList conjB = tablaconj_buscar(tabla, &claveB, aliasB);
          SList conjC = tablaconj_buscar(tabla, &claveC, aliasC);
          if (conjuntos_assert(conjB, conjC, aliasB, aliasC)) {
            lista = tablaconj_resta(conjB, conjC);
            lista->alias = alias;
            tablaconj_insertar(tabla, &clave, lista);
          } else {
              free(alias);
          }
        } else {
            printf("    ");
            printf("La operacion resta se ingresa de la siguiente manera:\n");
            printf("    ");
            printf("alias1 = alias2 - alias3\n");
            free(alias);
        }
        break;

      case COMPLEMENTO:
        if (compl_assert(comando)) {
          char *aliasCompl = comando_alias_compl(comando);
          int claveCompl = conseguir_clave(aliasCompl);
          SList conjB = tablaconj_buscar(tabla, &claveCompl, aliasCompl);
          if (conjB != NULL) {
            lista = tablaconj_compl(conjB);
            lista->alias = alias;
            tablaconj_insertar(tabla, &clave, lista);
            free(aliasCompl);
          } else {
              printf("    ");
              printf("No hay ningun conjunto relacionado con el alias %s\n",
                      aliasCompl);
              free(aliasCompl);
              free(alias);
          }
        } else {
            printf("    ");
            printf("La operacion complemento se ingresa de la "
                    "siguiente manera:\n");
            printf("    ");
            printf("alias1 = ~alias2\n");
            free(alias);
        }
        break;

      case IMPRIMIR:
        printf("    ");
        tablaconj_imprimir(tabla, &clave, alias, imprimir_conjunto);
        free(alias);
        break;

      case SALIR:
        tablaconj_destruir(tabla);
        break;
        
      case INVALIDO:
        printf("    ");
        printf("Comando invalido\n");
        break;

    }
  } while (opc != SALIR) ;
}

int main(int argc, char** argv) {
  if (argv[1] != NULL) {
    int bandera = 0;
    char *strTam = argv[1];
    for (int i = 0; strTam[i] != '\0' && !bandera; i++) {
      if ((isdigit(strTam[i]) == 0)) {
        bandera = 1;
      }
    }
    if (bandera) {
      printf("Argumento invalido, este debe ser un entero mayor a cero.\n");
      return 0;
    }
    int tam = atoi(strTam);
    if (tam > 0) {
      TablaConjuntos* tabla = tablaconj_crear(tam, hash);
      menu(tabla);
    } else {
        printf("Argumento invalido, este debe ser un entero mayor a cero.\n");
    }
  } else {
      printf("Debe haber un argumento numerico al correr el programa.\n");
  }
  return 0;
}