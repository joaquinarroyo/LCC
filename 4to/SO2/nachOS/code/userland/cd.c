#include "syscall.h"
#include "lib.c"

int
main(int argc, char *argv[])
{
    if (argc != 2) {
        Write("Usage: cd <directory>\n", 24, CONSOLE_OUTPUT);
        Exit(1);
    }
    int sector = Cd(argv[1]);
    if (sector == -1) {
        Write("cd: directory not found\n", 24, CONSOLE_OUTPUT);
        Exit(1);
    }
    return 0;
}