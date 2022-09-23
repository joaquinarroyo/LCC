#include "board.h"

int board_init(board_t *board, unsigned int height, unsigned int width) {
    if(height > 0 && width > 0) {
        board->height = height;
        board->width = width;
        board->boxes = malloc(sizeof(box_t)*height);
        for (int i = 0; i < height; i++) 
            board->boxes[i] = malloc(sizeof(box_t)*width);
        return 1;
    }
    return 0;
}

char board_get_round(board_t board, unsigned int height, unsigned int width) {
    if(height == -1){
        height = board.height - 1;
    }
    if(width == -1){
        width = board.width - 1;
    }
    if(height == board.height){
        height = 0;
    }
    if(width == board.width){
        width = 0;
    }

    return (board.boxes[height][width]).val;
}

void board_set(board_t *board, unsigned int height, unsigned int width, char val) {
    if (height < board->height && width < board->width) {  
        board->boxes[height][width].val = val;
    }
}

void board_load(board_t *board, char *str) {
    int i = 0, n = strlen(str);
    int height = 0, width = 0;
    while (i < n) {
        while (width < board->width) {
            board->boxes[height][width].val = str[i];
            if (str[i] == 'O') {
                board->boxes[height][width].state = 1;
            } else {
                board->boxes[height][width].state = 0;
            }
            width ++;
            i++;
        }
        width = 0;
        height ++;
    }
}

void board_destroy(board_t *board) {
    int altura = board->height, base = board->width;
    for (int i = 0; i < altura; i++) {
        free(board->boxes[i]);
    }
    free(board->boxes);
    free(board->sem);
}
