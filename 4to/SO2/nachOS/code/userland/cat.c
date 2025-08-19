#include "syscall.h"
#include "lib.c"

#define ARGC_ERROR    "Error: missing argument."
#define MAX_LINE 256

int
main(int argc, char *argv[])
{
    if (argc != 2) {
        Write(ARGC_ERROR, sizeof(ARGC_ERROR) - 1, CONSOLE_OUTPUT);
        Exit(1);
    }

    int success = 1;
    OpenFileId file = Open(argv[1]); // Chequear si el primer argumento es el propio archivo
    if (file < 0) {
        Write("Error: could not open file.\n", 27, CONSOLE_OUTPUT);
        Exit(1);
    }
    char line[MAX_LINE];
    int size = 0;

    while (Read(line, MAX_LINE, file) > 0) {
        puts2(line);
    }
    puts2("\n");

    Close(file);

    return 0;
}
