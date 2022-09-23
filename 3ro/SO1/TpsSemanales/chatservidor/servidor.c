/* Cabeceras de Sockets */
#include <sys/types.h>
#include <sys/socket.h>
/* Cabecera de direcciones por red */
#include <netinet/in.h>
/* Threads! */
#include <pthread.h>
/* Señales */
#include <signal.h>
/* **************** */
#include <unistd.h>

#include "comandos.h"
#define MAX_MSG 1024
#define MAX_CLIENTES 25

/* Enum con los estados de las casillas de la tabla de usuarios */
typedef enum {
  OCUP,
  FREE,
} ESTADO_CASILLA_TABLA;

/* Estructura de usuario */
typedef struct user_ {  
  int* socket;
  char* name;
} user;

/* Estructura de una casilla de la tabla de usuarios */
typedef struct casillaTabla_ {
  user* usuario;
  int state;
} casillaTabla;

/* Estructura de los argumentos de los hilos */
typedef struct args_ {
  casillaTabla* tablaUsers;
  int indexUser;
} args;

casillaTabla *tablaUsers; /* Variable global que representa a la tabla de usuarios */

void *trabajador(void *arg);

void error(char *msg);

void handler();

int main(int argc, char **argv){
  int sock, *soclient, *sockets;
  struct sockaddr_in servidor, clientedir;
  socklen_t clientelen;
  pthread_t thread;
  pthread_attr_t attr;

  if (argc <= 1) error("Faltan argumentos");

  /* Creamos el socket */
  if( (sock = socket(AF_INET, SOCK_STREAM, 0)) < 0 )
    error("Socket Init");

  /* Creamos a la dirección del servidor.*/
  servidor.sin_family = AF_INET;
  servidor.sin_addr.s_addr = INADDR_ANY;
  servidor.sin_port = htons(atoi(argv[1]));

  /* Inicializamos el socket */
  if (bind(sock, (struct sockaddr *) &servidor, sizeof(servidor)))
    error("Error en el bind");

  printf("Binding successful, and listening on %s\n",argv[1]);

  /************************************************************/
  /* Creamos los atributos para los hilos.*/
  pthread_attr_init(&attr);

  /* Hilos que no van a ser *joinables* */
  pthread_attr_setdetachstate(&attr,PTHREAD_CREATE_DETACHED);
  /************************************************************/

  /* Ya podemos aceptar conexiones */
  if(listen(sock, MAX_CLIENTES) == -1)
    error(" Listen error ");
  
  /* Creamos la tabla de usuarios y seteamos todas las casillas en LIBRE */
  tablaUsers = malloc(sizeof(casillaTabla)*MAX_CLIENTES);
  for (int i = 0; i < MAX_CLIENTES ; i++)
    tablaUsers[i].state = FREE;;

  for(;;){ /* Comenzamos con el bucle infinito*/
    /* Pedimos memoria para el socket */
    soclient = malloc(sizeof(int));

    /* Now we can accept connections as they come*/
    clientelen = sizeof(clientedir);
    if ((*soclient = accept(sock
                          , (struct sockaddr *) &clientedir
                          , &clientelen)) == -1)
      error("No se puedo aceptar la conexión. ");

    /* Inicializamos los argumentos del hilo */
    args argsThread;
    argsThread.tablaUsers = tablaUsers;

    int bandera = 1;
    /* Iteramos hasta encontrar la primer casilla libre */
    for (int i = 0; i < MAX_CLIENTES && bandera; i++) {
      if(tablaUsers[i].state == FREE) {
        /* Terminamos de completas los argumentos del hilo */
        argsThread.indexUser = i;

        /* Inicializamos el usuario */
        char * name = malloc(sizeof(char)*8); /* revisar el tamanio */
        sprintf(name, "%d", i);               /* pasamos el indexado como nombre de usuario */
        char* tmp = name;
        tmp = realloc(tmp, sizeof(char)*strlen(name));
        name = tmp;
        tablaUsers[i].usuario = malloc(sizeof(user));
        tablaUsers[i].usuario->socket = soclient;
        tablaUsers[i].usuario->name = name;
        tablaUsers[i].state = OCUP;
        bandera = 0;
      }
    }

    /* Le enviamos el socket al hijo*/
    pthread_create(&thread , NULL , trabajador, (void* )&argsThread);
  }
  /* Código muerto */
  close(sock);
  return 0;
}

void *trabajador(void *_arg){

  args *argsThread = _arg;
  tablaUsers = argsThread->tablaUsers;
  int indexUser = argsThread->indexUser;
  char *username = tablaUsers[indexUser].usuario->name;
  int sock = *(tablaUsers[indexUser].usuario->socket);
  char msg[MAX_MSG];

  printf("Se conecto: %s\n", username);

  /* Avisamos que esta conectado */
  char msgBienv[] = "Bienvenido, tu usuario es #";
  strcat(msgBienv, username);
  send(sock, msgBienv, sizeof(msgBienv)+sizeof(char), 0);

  /* Por si se cierra el servidor con ctrl+c */
  signal(SIGINT, handler);

  int bandera = 1;
  int caso;
  while(bandera) {
    /* Recibimos el mensaje */
    recv(sock, msg, sizeof(msg), 0);
    caso = ver_caso(msg);
    switch (caso)
    {
    case GLOBAL_MSG: ;
      char msgGen[MAX_MSG];

      /* Creamos el mensaje global */
      strcpy(msgGen, username);
      strcat(msgGen, ": "); /* 'username: ' */
      strcat(msgGen, msg);  /* 'username: msg' */

      int error = 0;
      for (int i = 0; i < MAX_CLIENTES; i++) {
        /* Iteramos en la tabla para encontrar todos los usuarios conectados */
        if (tablaUsers[i].state == OCUP) {
          int iSock = *(tablaUsers[i].usuario->socket);
          int nbytes = send(iSock, msgGen, sizeof(msgGen), 0);
          /* Revisamos si hubo error al enviar el mensaje */
          if (nbytes < 0) {
            printf("User[%s] to User[%s] --> Recv: %s [ERROR SENDING]\n", tablaUsers[indexUser].usuario->name, 
                                                                         tablaUsers[i].usuario->name, 
                                                                         msg);
            error = 1;
          }
        }
      }
      if (!error) {
        printf("User[%s] to [ALL] --> Recv: %s\n", tablaUsers[indexUser].usuario->name, msg);
      }
      memset(msgGen, '\0', MAX_MSG);
      break;
    case UNIQUE_MSG: ;
      char *destino = usuario_a_enviar(msg); /* destinatario */
      char *msgPriv = mensajes_unico(msg); /* mensaje para destinatario */

      /* Creamos el mensaje que recibira el destinatario */
      char msgDest[MAX_MSG];
      strcpy(msgDest, username);    /* 'username' */
      strcat(msgDest, " to you: "); /* 'username to you: ' */
      strcat(msgDest, msgPriv);     /* 'username to you: msgPriv ' */

      /* Creamos el mensaje que se le mostrara al remitente*/
      char msgRem[MAX_MSG];
      strcpy(msgRem, "You to ");    /* 'You to ' */
      strcat(msgRem, destino);      /* 'You to destino' */
      strcat(msgRem, ": ");         /* 'You to destino: ' */
      strcat(msgRem, msgPriv);      /* 'You to destino: msgPriv' */

      int enviado = 0;
      error = 0;
      for (int i = 0; i < MAX_CLIENTES; i++) {
        /* Buscamos una coincidencia entre destino y el nickname de algun usuario conectado */
        if (tablaUsers[i].state == OCUP) {
          /* Si hay coincidencia enviamos el mensaje */
          if (!strcmp(tablaUsers[i].usuario->name, destino)) {
            int iSock = *(tablaUsers[i].usuario->socket);
            int nbytes = send(iSock, msgDest, sizeof(msgDest), 0);
            enviado = 1;
            /* Revisamos si hubo error al enviar el mensaje */
            if (nbytes < 0) {
              printf("User[%s] to User[%s] --> Recv: %s [ERROR SENDING]\n", username, destino, msgPriv);
              send(iSock, "Error al enviar el mensaje", sizeof("Error al enviar el mensaje"), 0);
              error = 1;
            }
          }
        }
      }
      /* Si no hubo coincidencia se le enviara un mensaje al remitente avisandole */
      if (!enviado) {
        printf("User[%s] to User[%s] --> Recv: %s [USER NOT FOUND]\n", username, destino, msgPriv);
        send(sock, "Error, no se encontro el usuario", sizeof("Error, no se encontro el usuario"), 0);
      } else {
        /* Si se pudo enviar el mensaje se le enviara al remitente el mensaje correspondiente */
        send(sock, msgRem, sizeof(msgRem), 0);
      }
      if (!error && enviado) {
        printf("User[%s] to User[%s] --> Recv: %s\n", username, destino, msgPriv);
      }
      memset(msgDest, '\0', MAX_MSG);
      memset(msgRem, '\0', MAX_MSG);
      break;
    case CHANGE_NAME: ;
      char* newName = new_name(msg);
      int coincidencia = 0;
      for (int i = 0; i < MAX_CLIENTES; i++) {
        /* Buscamos si newName ya esta siendo utilizado */
        if (tablaUsers[i].state == OCUP) {
          /* Revisamos si hay coincidencia */
          if (!strcmp(tablaUsers[i].usuario->name, newName)) {
            coincidencia = 1;
          }
        }
      }
      if (coincidencia) {
        /* Si el nickname esta ocupado, avisamos */
        send(sock, "Nickname ocupado", sizeof("Nickname ocupado"), 0);
      } else {
        printf("User[%s] --> [CHANGE NICKNAME TO %s]\n", tablaUsers[indexUser].usuario->name,
                                                         newName);
        /* Si el nickname no esta ocupado, lo cambiamos y avisamos*/
        char* tmp = tablaUsers[indexUser].usuario->name;
        tmp = realloc(tmp, sizeof(char)*strlen(newName));
        tablaUsers[indexUser].usuario->name = tmp; 
        strcpy(tablaUsers[indexUser].usuario->name, newName);
        send(sock, "Nickname cambiado", sizeof("Nickname cambiado"), 0);
      }
      break;
    case EXIT: ;
      /* Avisamos a usuario que fue desconectado */
      send(sock, msg, sizeof(msg), 0);
      printf("User[%s] --> [EXIT]\n", tablaUsers[indexUser].usuario->name);

      /* Liberar socket para q pueda entrar otro */
      free(tablaUsers[indexUser].usuario->socket);
      free(tablaUsers[indexUser].usuario->name);
      free(tablaUsers[indexUser].usuario);
      tablaUsers[indexUser].state = FREE;
      bandera = 0;
      break;
    case INVALID: ;
      printf("User[%s] --> Recv: %s [INVALID]\n", tablaUsers[indexUser].usuario->name, msg);
      send(sock, "Comando invalido", sizeof("Comando invalido"), 0);
      break;
    }
    memset(msg, '\0', MAX_MSG);
  }
  return NULL;
}

/* Funcion que maneja el caso en el cual el servidor se cierra con ctrl+c */
void handler(){
  for(int i = 0; i < MAX_CLIENTES; i++) {
    /* Se cierran los clientes y se libera la memoria correspondiente */
    if (tablaUsers[i].state == OCUP) {
      send(*(tablaUsers[i].usuario->socket), "/exit", sizeof("/exit"), 0);
      free(tablaUsers[i].usuario->socket);
      free(tablaUsers[i].usuario->name);
      free(tablaUsers[i].usuario);
      tablaUsers[i].state = FREE;
    }
  }
  free(tablaUsers);
  exit(1);
}

void error(char *msg){
  exit((perror(msg), 1));
}
