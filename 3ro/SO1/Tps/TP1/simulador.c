#include "gameDef.h"

/* Funcion principal que ejecuta el programa */

int main(int argc, char** argv) {
    game_t *juego = loadGame(argv[1]);
    juego->board = congwayGoL(juego->board, juego->cycles, get_nprocs());
    writeBoard(juego->board[0], "salida.txt");
    board_destroy(juego->board);
    free(juego);
    return 0;
}