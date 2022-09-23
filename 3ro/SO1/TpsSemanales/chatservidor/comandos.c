#include "comandos.h"

int ver_caso(char* comando) {
    char* copia = malloc(sizeof(comando));
    strcpy(copia, comando);
    if (comando[0] == '/') {
        char divisor = ' ';
        char* token = strtok(copia, &divisor);
        if (!strcmp(token, "/msg")) {
            return UNIQUE_MSG;
        }
        if (!strcmp(token, "/nickname")) {
            return CHANGE_NAME;
        }
        if (!strcmp(token, "/exit")) {
            return EXIT;
        }
        return INVALID;
    } else {
        return GLOBAL_MSG;
    }
}

char* usuario_a_enviar(char* comando) {
    char* copia = malloc(sizeof(comando)+sizeof(char));
    strcpy(copia, comando);
    char divisor = ' ';
    char* token = strtok(copia, &divisor);

    /* Tomamos el user */
    token = strtok(NULL, &divisor);
    char *username = malloc(sizeof(token)+sizeof(char));
    strcpy(username, token);

    return username;
}

char* mensajes_unico(char* comando) {
    char* copia = malloc(sizeof(comando)+sizeof(char));
    strcpy(copia, comando);
    char divisor = ' ';
    char* token = strtok(copia, &divisor);
    token = strtok(NULL, &divisor);

    /* Tomamos el mensaje */
    divisor = '\0';
    token = strtok(NULL, &divisor);
    char* msg = malloc(sizeof(token)+sizeof(char));
    strcpy(msg, token);
    return msg;
}

char* new_name(char* comando) {
    char divisor = ' ';
    char* copia = malloc(sizeof(comando)+sizeof(char));
    strcpy(copia, comando);
    char* token = strtok(copia, &divisor);
    
    /* Tomamos el nuevo nickname y lo retornamos */
    token = strtok(NULL, &divisor);
    char *newName = malloc(sizeof(token)+sizeof(char));
    strcpy(newName, token);
    return newName;
}