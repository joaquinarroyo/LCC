#include "syscall.h"

#define ARGC_ERROR    "Error: missing argument."
#define MAX_LINE 256

int
main(int argc, char *argv[])
{
    Create("hola");
    OpenFileId newFile = Open("hola"); // Chequear si el primer argumento es el propio archivo
    for(int i = 0; i<300; i++) {
        Write("This is the spring of our discontent.\n", 
                sizeof "This is the spring of our discontent.\n", newFile);
    }
    Close(newFile);
    return 0;
}
