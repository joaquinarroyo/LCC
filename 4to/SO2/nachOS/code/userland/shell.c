#include "syscall.h"
#include "lib.c"

#define MAX_LINE_SIZE  60
#define MAX_PATH_SIZE 128
#define MAX_ARG_COUNT  32
#define ARG_SEPARATOR  ' '

#define NULL  ((void *) 0)

static inline void
WritePrompt(OpenFileId output, const char *cwd)
{
    static const char PROMPT[] = "shell $ ";
    Write("~", 1, output);
    if (cwd[0] != '\0')
        Write(cwd, strlen(cwd), output);
    Write("\n", 1, output);
    Write(PROMPT, sizeof PROMPT - 1, output);
}

static inline void
WriteError(const char *description, OpenFileId output)
{
    static const char PREFIX[] = "Error: ";
    static const char SUFFIX[] = "\n";

    Write(PREFIX, sizeof PREFIX - 1, output);
    Write(description, strlen(description), output);
    Write(SUFFIX, sizeof SUFFIX - 1, output);
}

static unsigned
ReadLine(char *buffer, unsigned size, OpenFileId input)
{
    unsigned i;
    for (i = 0; i < size; i++) {
        Read(&buffer[i], 1, input);
        if (buffer[i] == '\n') {
            buffer[i] = '\0';
            break;
        }
    }
    
    return i;
}

static int
PrepareArguments(char *line, char **argv, unsigned argvSize)
{
    unsigned argCount;

    argv[0] = line;
    argCount = 1;

    // Traverse the whole line and replace spaces between arguments by null
    // characters, so as to be able to treat each argument as a standalone
    // string.
    for (unsigned i = 0; line[i] != '\0'; i++) {
        if (line[i] == ARG_SEPARATOR) {
            if (argCount == argvSize - 1) {
                // The maximum of allowed arguments is exceeded, and
                // therefore the size of `argv` is too.  Note that 1 is
                // decreased in order to leave space for the NULL at the end.
                return 0;
            }
            line[i] = '\0';
            argv[argCount] = &line[i + 1];
            argCount++;
        }
    }

    argv[argCount] = NULL;
    return 1;
}

int
main(void)
{
    const OpenFileId INPUT  = CONSOLE_INPUT;
    const OpenFileId OUTPUT = CONSOLE_OUTPUT;
    char line[MAX_LINE_SIZE];
    char *argv[MAX_ARG_COUNT];
    char cwd[MAX_PATH_SIZE];
    cwd[0] = '/'; cwd[1] = '\0'; // Initialize cwd to root

    for (;;) {
        WritePrompt(OUTPUT, cwd);
        const unsigned lineSize = ReadLine(line, MAX_LINE_SIZE, INPUT);

        if (lineSize == 0) {
            continue;
        }

        if (PrepareArguments(line, argv, MAX_ARG_COUNT) == 0) {
            WriteError("too many arguments.", OUTPUT);
            continue;
        }

        // Comment and uncomment according to whether command line arguments
        // are given in the system call or not.
        if (line[strlen(line)-1] == '&') {
            SpaceId newProc = Exec(argv[0], argv, 0);
        } else if (mystrcmp(argv[0], "cd") == 0) {
            if (argv[1] == NULL) {
                WriteError("cd: missing argument", OUTPUT);
                continue;
            }

            int result = Cd(argv[1]);
            if (result == -1) {
                WriteError("cd: directory not found", OUTPUT);
            } else {
                // Si la ruta es absoluta, cwd = esa ruta
                if (argv[1][0] == '/') {
                    mystrcpy(cwd, argv[1], MAX_PATH_SIZE);
                } else if (cwd[0] == '/' && cwd[1] == '\0') {
                    mystrcpy(cwd, "/", MAX_PATH_SIZE);
                    mystrcat(cwd, argv[1], MAX_PATH_SIZE);
                } else {
                    mystrcat(cwd, "/", MAX_PATH_SIZE);
                    mystrcat(cwd, argv[1], MAX_PATH_SIZE);
                }
            }
        } else {
            SpaceId newProc = Exec(argv[0], argv, 1);
            if(newProc != -1)
                Join(newProc);
        }
    }

    // Never reached.
    return -1;
}
