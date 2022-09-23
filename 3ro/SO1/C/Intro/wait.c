#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <wait.h>

int main(int argc, char** argv){
    pid_t p = fork();

    if (p < 0) {
        perror("Error\n");
    }

    if (p == 0) {
        printf("[ Child ] %d \n", getpid());
        sleep(2);
        _exit(0);
    } else {
        int status;
        printf("[ Parent ] %d\n", getpid());
        wait(&status);
        if (WIFEXITED(status)) {
            printf("Exito \n");
            printf("Child resulto en %d \n", WEXITSTATUS(status));
        } else {
            printf(":( \n");
        }
    }
    

    return 0;
}