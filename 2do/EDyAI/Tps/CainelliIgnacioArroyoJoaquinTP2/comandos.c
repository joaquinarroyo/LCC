#include "comandos.h"
#include "itree.h"

/**
 * Recibe un arreglo de caracteres y dos enteros, y revisa que 
 * los caracteres que deberian representar a numeros, sean, 
 * efectivamente, caracteres numericos.
 */ 
int number_assert(char *comando, int i, int cantNum) {
   int error = 0, j = 0;
   while (j < cantNum && !error) {
     if ((isdigit(comando[i]) == 0)
           && (comando[i] != '.' && comando[i] != '-')) {
       error = 1;
     }
     i++;
     j++;
   }
   return error;
 }
  int opcion(char *comando) {
   int opc;
   if (comando[0] == 'i') {
     opc = 1;
   }
   
  else if (comando[0] == 'e') {
     opc = 2;
   }
   
  else if (comando[0] == '?') {
     opc = 3;
   }
   
  else if (!(strcmp(comando, "dfs"))) {
     opc = 4;
   }
   
  else if (!(strcmp(comando, "bfs"))) {
     opc = 5;
   }
   
  else if (!(strcmp(comando, "salir"))) {
     opc = 6;
   }
   
  else
    opc = 0;
   return opc;
 }
  int cant_num(char *linea, int i) {
   int contador = 0;
   while (linea[i] != ',' && linea[i] != ']') {
     i++;
     contador++;
   }
   return contador;
 }
  void consola_intervalo(char *linea, Interval intervalo) {
   int i = 0, j = 0, cantNum;
   char *temp;
   while (linea[i] != '[') {
     i++;
   }
   i++;
   cantNum = cant_num(linea, i) + 1;
   temp = malloc(sizeof(char) * cantNum);
   while (linea[i] != ',') {
     temp[j] = linea[i];
     i++;
     j++;
   }
   temp[j] = '\0';
   intervalo->extIzq = atof(temp);
   i += 2;
   j = 0;
   free(temp);
   cantNum = cant_num(linea, i) + 1;
   temp = malloc(sizeof(char) * cantNum);
   while (linea[i] != ']') {
     temp[j] = linea[i];
     i++;
     j++;
   }
   temp[j] = '\0';
   intervalo->extDer = atof(temp);
   free(temp);
 }
  int variable_assert(char *comando) {
   int i = 3, cantNum;
   if (comando[2] != '[') {
     return 0;
   }
   cantNum = cant_num(comando, i);
   if (cantNum >= MAX_CARAC) {
     return 0;
   }
   if (number_assert(comando, i, cantNum) || cantNum == 0) {
     return 0;
   }
   if (comando[i + cantNum] != ',' || comando[i + cantNum + 1] != ' ') {
     return 0;
   }
   i += cantNum + 2;
   cantNum = cant_num(comando, i);
   if (cantNum >= MAX_CARAC) {
     return 0;
   }
   if (number_assert(comando, i, cantNum) || cantNum == 0) {
     return 0;
   }
   i += cantNum;
   if (comando[i] != ']') {
     return 0;
   }
   return 1;
 }
  int interval_assert(Interval intervalo) {
   if (intervalo->extIzq > intervalo->extDer) {
     return 0;
   }
   
  else
    return 1;
 }
  void verificar_interseccion(ITree nodo, FuncionVisitante visit) {
   if (itree_es_vacio(nodo)) {
     printf("No");
   }
   
  else {
     printf("Si, ");
     visit(nodo);
   }
 }

  
