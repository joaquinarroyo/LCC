/* Cabeceras de Sockets */
#include <sys/types.h>
#include <sys/socket.h>
/* Cabecera de direcciones por red */
#include <netdb.h>
/* Cabeceras estandar */
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
/* Hilos */
#include <pthread.h>
/* Señales */
#include <signal.h>

#define MAX_MSG 1024

int sock;            /* Variable global que representa al socket del servidor */
pthread_t thread[2]; /* Variable global que representa a los threads */

/*
  El archivo describe un sencillo cliente que se conecta al servidor establecido
  en el archivo RemoteServer.c. Se utiliza de la siguiente manera:
  ./cliente IP port
 */

void *entrada(void *_arg);

void *salida(void *_arg);

void handler();

void error(char *msg){
  exit((perror(msg), 1));
}

int main(int argc, char **argv){
  char buf[MAX_MSG];
  struct addrinfo *resultado;
  pthread_attr_t attr;

  /* Creamos los atributos para los hilos.*/
  pthread_attr_init(&attr);

  /* Hilos que no van a ser *joinables* */
  pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);

  /*Chequeamos mínimamente que los argumentos fueron pasados*/
  if(argc != 3){
    fprintf(stderr,"El uso es \'%s IP port\'", argv[0]);
    exit(1);
  }

  /* Inicializamos el socket */
  if( (sock = socket(AF_INET , SOCK_STREAM, 0)) < 0 )
    error("No se pudo iniciar el socket");

  /* Buscamos la dirección del hostname:port */
  if (getaddrinfo(argv[1], argv[2], NULL, &resultado)){
    fprintf(stderr,"No se encontro el host: %s \n",argv[1]);
    exit(2);
  }

  /* Nos conectamos con el server */
  if(connect(sock, (struct sockaddr *) resultado->ai_addr, resultado->ai_addrlen) != 0)
    error("No se pudo conectar ");

  printf("La conexión fue un éxito\n");

  /* Creamos dos hilos donde uno maneja la entrada del cliente, y otro la salida */
  pthread_create(&thread[0] , NULL , entrada, (void*)&sock);
  pthread_create(&thread[1] , NULL , salida, (void*)&sock);

  /* Esperamos que terminen los hilos */
  for (int i = 0; i < 2; i++) {
    if (pthread_join(thread[i], NULL) != 0) {
      perror("Fallo la espera de un hilo\n");
      exit(EXIT_FAILURE);
    }
  }

  /* Cerramos :D!*/
  freeaddrinfo(resultado);
  close(sock);
  return 0;
}

/* Funcion que maneja la entrada del cliente */
void *entrada(void *_arg) {
  int sock = *(int *)_arg;
  int bandera = 1;
  char msg[MAX_MSG];
  
  /* Bucle en el cual el cliente se va a quedar esperando un mensaje 
    del el servidor*/
  while(bandera) {
    memset(msg, '\0', sizeof(msg));
    recv(sock, msg, sizeof(msg), 0);
    if (!strcmp(msg, "/exit")) {
      printf("Te has desconectado\n");
      bandera = 0;
    } else {
      printf("%s\n", msg);
    }
    memset(msg, '\0', sizeof(msg));
  }

  /* Cuando salimos del bucle, quiere decir que el cliente se desconecto, 
    por lo tanto cancelamos el thread que maneja la salida del cliente para 
    que el programa pueda terminar */
  pthread_cancel(thread[1]);  
  return NULL;
}

/* Funcion que maneja la salida del cliente */
void *salida(void *_arg) {
  int sock = *(int *)_arg;
  char msg[MAX_MSG];
  /* Bucle en el cual el cliente va a mandar mensajes al servidor */
  while(1) {
    memset(msg, '\0', sizeof(msg));
    scanf(" %[^\n]", msg);
    // int index = strlen(msg);
    // msg[index] = '\0';
    send(sock, msg, sizeof(char)*(strlen(msg)), 0);
    memset(msg, '\0', sizeof(msg));
  }
  /* Dead code */
  return NULL;
}
