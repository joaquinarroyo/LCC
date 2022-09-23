#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <wait.h>
#define MAXSTR 150
#define MAXVAR 20

/*
Trabajo pseudo-terminal - Cainelli Ignacio y Arroyo Joaquin.
*/

/*
Funcion que recibe como argumento un char pointer, el cual representa al ejecutable del programa.
Simula el funcionamiento de una terminal, en la cual solo podemos ejecutar programas, con sus respectivos argumentos,
y además, podemos utilizar el argumento & para correr el programa en segundo plano.
El programa termina al utilizar el comando "exit".
*/
void terminal(char* terminal){
    pid_t estado;
    char linea[MAXSTR];
    char* args[MAXVAR];
    char* direccion;

    printf("\x1b[32m" "Usuario:~$ " "\x1b[0m"); //Print en color verde
    scanf("%[^\n]", linea);

    if (strcmp(linea, "exit") == 0) {
        return ;
    }
    
    char divisor[2] = " ";
    char* token = strtok(linea, divisor);
    int longitud;

    if (token != NULL) {            // Direccion del programa a ejecutar
        longitud = strlen(token);   
        direccion = malloc(sizeof(char)*longitud);
        strcpy(direccion, token);
        token = strtok(NULL, divisor);
    }

    int i = 1;
    args[0] = direccion;    
    while (token != NULL) {             // Argumentos del programa a ejecutar
        longitud = strlen(token);
        args[i] = malloc(sizeof(char)*longitud);
        strcpy(args[i], token);
        token = strtok(NULL, divisor);
        i++;
    }
    args[i] = NULL;

    int ampersand = 0;
    if (i != 1) {
        if (strcmp(args[i-1], "&") == 0) {
            ampersand = 1;
        }
    }
    
    
    char* argsT[1];         // Argumentos del exec de la terminal
    argsT[0] = terminal;    
    argsT[1] = NULL;

    int res;
    if (!ampersand) {
        estado = fork();
        if (estado == 0) {
            res = execv(direccion, args);
            if (res < 0) {
                perror("\x1b[31m" "Error" "\x1b[0m");
                exit(EXIT_FAILURE);
            }
            _exit(0);
        } else {
            int status;
            wait(&status);  
            if (WIFEXITED(status)) {    // Liberamos la memoria que el proceso parent no utiliza
                for (int k = 0; k < i; k++) {
                    free(args[k]);
                }
                execv(terminal, argsT);
            }
        }
    } else {
        estado = fork();
        if (estado == 0) {
            res = execv(direccion, args);
            if (res < 0) {
                perror("\x1b[31m" "Error" "\x1b[0m");
                exit(EXIT_FAILURE);
            }
            _exit(0);
        } else {
            for (int k = 0; k < i; k++) {
                free(args[k]);
            }
            execv(terminal, argsT);
        }
    }
}

int main(int argc, char** argv){
    terminal(argv[0]);
    return 0;
}