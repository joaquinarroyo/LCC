#include "syscall.h"

#define ARGC_ERROR    "CP Error: missing argument.\n"
#define SRC_ERROR    "CP Error: couldn't open src.\n"
#define DEST_ERROR    "CP Error: couldn't create dest.\n"
#define MAX_LINE 256


int
main(int argc, char *argv[])
{
    OpenFileId src;
    OpenFileId dest;
    char line[MAX_LINE];
    int size = 0;

    if (argc != 3) {
        Write(ARGC_ERROR, sizeof(ARGC_ERROR) - 1, CONSOLE_OUTPUT);
        Exit(1);
    }

    src = Open(argv[1]);
    if(src != -1 && Create(argv[2]) != -1) {
        dest = Open(argv[2]);

        do {
            size = Read(line, 1, src);
            if (size > 0) {
                Write(line, 1, dest);
            }
        } while (size > 0);

        Close(src);
        Close(dest);
    }else {
        if(src != -1)
            Write(SRC_ERROR, sizeof(SRC_ERROR) - 1, CONSOLE_OUTPUT);
        else
            Write(DEST_ERROR, sizeof(DEST_ERROR) - 1, CONSOLE_OUTPUT);
        Exit(1);
    }
    return 0;
}
