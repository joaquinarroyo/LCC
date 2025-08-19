#include "syscall.h"
#include "lib.c"

#define ARGC_ERROR    "Error: missing argument.\n"

int
main(int argc, char *argv[])
{
    if (argc != 2) {
        Write(ARGC_ERROR, sizeof(ARGC_ERROR) - 1, CONSOLE_OUTPUT);
        Exit(1);
    }

    Create(argv[1]);

    return 0;
}