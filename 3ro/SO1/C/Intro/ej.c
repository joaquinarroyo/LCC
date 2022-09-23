#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>

int bin(char* direccion, int segundos){
    char** args = NULL;
    pid_t estado;
    while(1){
        estado = fork();
        sleep(segundos);
        if (estado == 0){
            execv(direccion, args);
            _exit(0);
        }
    }
    return 0;
}

int main(int argc, char** argv){
    if(argc != 3){
        return 0;
    }
    bin(argv[1], atoi(argv[2]));
    return 0;
}