#include "itree.h"
#include "comandos.h"

/**
 * Recibe un nodo e imprime su intervalo.
 */
void imprimir_intervalo(ITree nodo) {
  printf("[%.2f, %.2f] ", nodo->interval->extIzq, nodo->interval->extDer);
}

/**
 * Recibe un arbol y opera con el segun los comandos que se van recibiendo 
 * desde la consola.
 */
void menu(ITree arbol) {
  int opc;
  do {
    char *comando = malloc(sizeof(char) * MAX_CARAC);
    scanf(" %[^\n]", comando);
    int n = strlen(comando);
    char *temp;
    temp = realloc(comando, sizeof(char) * (n + 1));
    comando = temp;
    opc = opcion(comando);
    switch (opc) {
      //Caso para insertar.
    case 1:
      if (variable_assert(comando)) {
        Interval intervalo1 = malloc(sizeof(Intervalo));
        consola_intervalo(comando, intervalo1);
        if (interval_assert(intervalo1)) {
          arbol = itree_insertar(arbol, intervalo1);
        } else {
          printf("El extremo izquierdo del intervalo debe ser menor al "
                 "extremo derecho\n");
          free(intervalo1);
        }
      } else {
        printf("Argumentos invalidos\n");
        printf("La funcion se utiliza de la forma i [double, double]\n");
      }
      break;
      //Caso para eliminar.
    case 2:
      if (variable_assert(comando)) {
        Interval intervalo2 = malloc(sizeof(Intervalo));
        consola_intervalo(comando, intervalo2);
        if (interval_assert(intervalo2)) {
          arbol = itree_eliminar(arbol, intervalo2);
          free(intervalo2);
        } else {
          printf("El extremo izquierdo del intervalo debe ser menor al "
                 "extremo dererecho\n");
          free(intervalo2);
        }
      } else {
        printf("Argumentos invalidos\n");
        printf("La funcion se utiliza de la forma e [double, double]\n");
      }
      break;
      //Caso para intersecar.
    case 3:
      if (variable_assert(comando)) {
        Interval intervalo3 = malloc(sizeof(Intervalo));
        consola_intervalo(comando, intervalo3);
        if (interval_assert(intervalo3)) {
          ITree interseccion = itree_intersectar(arbol, intervalo3);
          printf("  ");
          verificar_interseccion(interseccion, imprimir_intervalo);
          printf("\n");
          free(intervalo3);
        } else {
          printf("El extremo izquierdo del intervalo debe ser menor al "
                 "extremo derecho\n");
          free(intervalo3);
        }
      } else {
        printf("Argumentos invalidos\n");
        printf("La funcion se utiliza de la forma ? [double, double]\n");
      }
      break;
      //Caso para imprimir recorriendo primero en profundidad.
    case 4:
      printf("  ");
      itree_recorrer_dfs(arbol, itree_inorder, imprimir_intervalo);
      printf("\n");
      break;
      //Caso para imprimir recorriendo primero a lo ancho.
    case 5:
      printf("  ");
      itree_recorrer_bfs(arbol, imprimir_intervalo);
      printf("\n");
      break;
      //Caso para salir del programa.
    case 6:
      itree_destruir(arbol);
      break;
      //Caso default.
    default:
      printf("Comando invalido\n");
      break;
    }
    free(comando);
  } while (opc != 6);
}

int main() {
  ITree arbol = itree_crear();
  menu(arbol);
  return 0;
}
