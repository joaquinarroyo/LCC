#include "syscall.h"

#define ARGC_ERROR    "Error: missing argument."
#define OPEN_ERROR    "Error: cannot open file."

static int mystrlen(const char *s) {
    int i = 0;
    while (s[i] != '\0') i++;
    return i;
}

int
main(int argc, char *argv[])
{
    if (argc != 3) {
        Write(ARGC_ERROR, sizeof(ARGC_ERROR) - 1, CONSOLE_OUTPUT);
        Exit(1);
    }

    OpenFileId file = Open(argv[1]);
    if (file == -1) {
        file = Create(argv[1]);
        file = Open(argv[1]);
        if (file == -1) {
            Write(OPEN_ERROR, sizeof(OPEN_ERROR) - 1, CONSOLE_OUTPUT);
            Exit(1);
        }
    }

    Write(argv[2], mystrlen(argv[2]), file);
    Write("\n", 1, file);

    Close(file);

    return 0;
}