#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>

int main(int argc, char** argv){
    char** args = NULL;
    int res = 0;
    printf("Se ejecuto programa con PID %d\n", getpid());
    res = execv("./getpid", args);
    if (res < 0) {
        perror("Algo fallo.\n");
    }

    return 0;
}