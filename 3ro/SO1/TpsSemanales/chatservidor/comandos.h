#ifndef __COMANDOS_H__
#define __COMANDOS_H__
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

/* Enum con los casos de los comandos que envia el
  cliente al server */
typedef enum {
  GLOBAL_MSG,
  UNIQUE_MSG,
  CHANGE_NAME,
  INVALID,
  EXIT,
} CASOS_COMANDOS;

/* Funcion que recibe el comando de parte del cliente, y devuelve que tipo de comando es */
int ver_caso(char* comando);

/* Funcion que recibe el comando de la forma '/msg user mensaje' , y devuelve el user */
char* usuario_a_enviar(char* comando);

/* Funcion que recibe el comando de la forma '/msg user mensaje' , y devuelve el mensaje */
char* mensajes_unico(char* comando);

/* Funcion que recibe un comando particular, el caso de /nickname newName
    Lo que hace es tomar el newName y devolverlo */
char* new_name(char* comando);

#endif