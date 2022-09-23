#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>

int main(int argc, char** argv){
    pid_t p;
    p = fork();
    if (p < 0) {
        perror("Error\n");
    }

    // ^^^^^^^^ Se comparte
    if (p == 0) {
        printf("Proceso child con PID %d\n", getpid());
        _exit(0);
    } else {
        printf("Proceso parent con PID %d\n", getpid());
    }
    
    return 0;
}