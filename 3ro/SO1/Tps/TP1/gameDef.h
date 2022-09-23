#ifndef __GAMEDEF_H__
#define __GAMEDEF_H__
#include "board.h"
#include <ctype.h>
#include <pthread.h>
#include <sys/sysinfo.h>
#include <unistd.h>
#define MAX 200

/******************************************************************************/
/* Representamos las células vivas como 'O' y las muertas como 'X' */

enum State {DEAD, ALIVE};   /* enum de los estados de las celulas */
enum State_Threads{TO_UPDATE, UPDATED}; /* enum de los estados de los hilos */

/* Tipo de funcion creada para poder aplicar una determinada FuncionRegla a un bloque 
    de filas */
typedef void (*FuncionRegla) (board_t *board, unsigned int height, unsigned int width);

/******************************************************************************/
/* Definición de la estructura de los argumentos de cada hilo */
typedef struct _args {
    board_t *board;
    int *contador;
    int *state_threads;
    int i;
    int cycles;
    int nuproc;
} args_t;

/******************************************************************************/
/* Definición de la estructura de datos del juego */
typedef struct _game {
    board_t* board;
    int cycles;
} game_t ;

/******************************************************************************/

/* Cargamos el juego desde un archivo */
game_t *loadGame(const char *filename);

/* Guardamos el tablero 'board' en el archivo 'filename' */
void writeBoard(board_t board, const char *filename);

/* Simulamos el Juego de la Vida de Conway con tablero 'board' la cantidad de
ciclos indicados en 'cycles' en 'nuprocs' unidades de procesamiento*/
board_t *congwayGoL(board_t *board, unsigned int cycles, const int nuproc);

#endif
