#ifndef __BOARD_H__
#define __BOARD_H__
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <semaphore.h>

/******************************************************************************/
/* Definición de la estructura de datos del tablero */
typedef struct _box {
    int state;
    char val;
} box_t;

typedef struct _board {
    unsigned int height;
    unsigned int width;
    box_t **boxes;
    sem_t *sem;
    sem_t mutex;
} board_t;

/******************************************************************************/
/******************************************************************************/

/* Funciones sobre el tablero */

/* Creación del tablero */
int board_init(board_t *board, unsigned int height, unsigned int width);

/* Leer el tablero en una posición asumiendo que el tablero es 'redondo'.*/
char board_get_round(board_t board, unsigned int height, unsigned int width);

/* Asignarle un valor 'val' a la posición (height, width) del tablero asumiendo que la posicion dada
    esta entre la altura y la base del tablero */
void board_set(board_t *board, unsigned int height, unsigned int width, char val);

/* Leer de una lista de caracteres e interpretarla como un tablero */
void board_load(board_t *board, char *str);

/* Destroy board */
void board_destroy(board_t *board);

#endif