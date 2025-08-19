#include "syscall.h"

#define ARGC_ERROR    "Error: missing argument.\n"
#define REMOVE_ERROR  "Error: could not remove file.\n"

int
main(int argc, char *argv[])
{
    if (argc != 2) {
        Write(ARGC_ERROR, sizeof(ARGC_ERROR) - 1, CONSOLE_OUTPUT);
        Exit(1);
    }

    for (int i=1; i<argc; i++) {
        if (Remove(argv[i]) < 0) {
            Write(REMOVE_ERROR, sizeof(REMOVE_ERROR) - 1, CONSOLE_OUTPUT);
        }
    }
    return 0;
}
