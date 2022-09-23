#include "gameDef.h"

/******************************************************************************/
/* funciones auxiliares de lectura de archivo */

/* Chequea que la linea tenga el formato correcto */
int chequear_linea(char* linea, int i) {
    if (!isdigit(linea[i]) && (linea[i+1] != 'X' || linea[i+1] != 'O' || linea[i+1] != '\n')) {
        perror("\x1b[31mError: \x1b[0m Formato del tablero incorrecto\n");
        return 0;
    }
    return 1;
}

/* Devuelve el tamaño que debe tener el arreglo que representa al tablero */
void tam_tablero(FILE *fp, int dimensiones[]) {
    char buff[MAX];
    int contador = 0, casillas = 0, filas = 0;
    while (fgets(buff, MAX, (FILE *) fp)) {
        if (contador != 0) {       
            int longitud = strlen(buff) - 2, i = 0;
            while (i < longitud) {
                if(chequear_linea(buff, i)) {
                    casillas += atoi(&buff[i]);
                } else {
                    exit(EXIT_FAILURE);
                }
                i+=2;
            }
            filas++;
        }
        contador ++;
    }
    dimensiones[0] = casillas;
    dimensiones[1] = filas;
}

/* Lee el archivo y completa el arreglo de enteros que representa a la cabecera del archivo
    y al arreglo de caracteres que representa al tablero con sus respectivos datos */
void leer_archivo(FILE *fp, int *cabecera, char *tablero, int tam) {
  char buff[MAX];
  int contador = 0, i = 0, j = 0, cantidad = 0, longitud;

  while (fgets(buff, MAX, (FILE *) fp)) {
    if (contador == 0) {
        char divisor = ' ';
        char* token = strtok(buff, &divisor);
        while (token != NULL) {
            cabecera[i] = atoi(token);
            token = strtok(NULL, &divisor);
            i++;
        }
    } else {
        if (tam != cabecera[1] * cabecera[2]) {
            perror("\x1b[31mError:\x1b[0m No coinciden las dimensiones del tablero con la cantidad de celulas\n");
            exit(EXIT_FAILURE);
        }
        int longitud = strlen(buff) - 2;
        i = 0;
        while (i < longitud) {
            cantidad += atoi(&buff[i]);
            i++;
            while (j < cantidad) {
                tablero[j] = buff[i];
                j++;
            }
            i++;
        }
    }
    contador ++;
  }
}

/******************************************************************************/
/* funciones auxiliares del Juego de la Vida */

/* Devuelve la cantidad de vecinos vivos de una celula en la posicion (height, width) */
unsigned int neighbors_get(board_t board, unsigned int height, unsigned int width) {
    unsigned int neighbors = 0;
    int height2 = height;
    int width2 = width;
    for (int i = -1; i <= 1; i++) {
        for (int j = -1; j <= 1; j++) {
            if (i != 0 || j != 0) {
                if (height2 < 0) {
                    height2 = board.height - 1;
                }
                if (width2 < 0) {
                    width2 = board.width - 1;
                }
                if (board_get_round(board, height2+i, width2+j) == 'O') {
                    neighbors++;
                }
            }
        }
    }
    return neighbors;
}

/* Cambia el estado de una celula en la posicion (height, width) segun su cantidad de vecinos vivos */
void change_state(board_t *board, unsigned int height, unsigned int width) {
    board_t boardtmp = board[0];
    unsigned int neighbors = neighbors_get(boardtmp, height, width);
    if (board_get_round(boardtmp,height,width) == 'O') {
        if (neighbors >= 4 || neighbors <= 1) {
            board->boxes[height][width].state = DEAD;
        }
    } else {
        if (neighbors == 3) {
            board->boxes[height][width].state = ALIVE;
        }
    }
}

/* Cambia el valor de una celula en la posicion (height, width) segun su estado */
void change_val(board_t *board, unsigned int height, unsigned int width) {
    if (board->boxes[height][width].state == DEAD) {
        board_set(board, height, width, 'X');
    } else {
        board_set(board, height, width, 'O');
    }
}

/* Chequea que todos los hilos hayan actualizado sus estados */
int all_updated(int *state_thr, const int nuproc) {
    int bandera = 1;
    for (int i = 0; i < nuproc && bandera; i++) {
        if (state_thr[i] != UPDATED) {
            bandera = 0;
        }
    }
    return bandera;
}

/******************************************************************************/
/* funciones principales de lectura y escritura de archivo */

game_t *loadGame(const char *filename) {
    FILE *fp;
    fp = fopen(filename, "r");

    int dimensiones[2];
    tam_tablero(fp, dimensiones);
    int casillas = dimensiones[0];
    int filas = dimensiones[1];

    unsigned int *cabecera = malloc(sizeof(int)*3);
    char *tablero = malloc(sizeof(char)*casillas);

    fseek(fp, 0, SEEK_SET);
    /* Leemos el archivo y chequeamos las dimensiones */
    leer_archivo(fp, cabecera, tablero, casillas);   
    
    if (filas != cabecera [1]) {
        perror("\x1b[31mError:\x1b[0m No coinciden las dimensiones del tablero\n");
        exit(EXIT_FAILURE);
    }

    /* Creación del juego */
    game_t *juego = malloc(sizeof(game_t));   

    /* Guardamos la cantidad de ciclos */
    juego->cycles = cabecera[0];

    /* Creamos el tablero y lo inicializamos con sus respectivas dimensiones */    
    board_t *board = malloc(sizeof(board_t));

    if (!board_init(board, cabecera[1], cabecera[2])){
        perror("\x1b[31mError:\x1b[0m Fallo la inicializacion del tablero\n");
        exit(EXIT_FAILURE);
    }
    
    juego->board = board;

    /* Cargamos el tablero al juego */
    board_load(juego->board, tablero);
    return juego;
}

void writeBoard(board_t board, const char *filename) {
    FILE *fp = fopen(filename, "w");
    int tam = board.height * board.width;
    int height = 0, width = 0, i = 0, contador = 0;
    while (i < tam) {
        char val = board.boxes[height][width].val;
        while (width < board.width + 1) {
            if (val != board.boxes[height][width].val) {
                if (width == board.width + 1) {
                    contador ++;
                }
                fprintf(fp, "%d", contador);
                fputc(val, fp);
                val = board.boxes[height][width].val;
                contador = 0;
            }
            contador ++;
            width++;
            i++;
        }
        fputc('\n', fp);
        contador = 0;
        width = 0;
        height ++;
    }
}

/******************************************************************************/
/* funciones principales del Juego de la Vida */

/* Aplica la regla recibida como argumento funcion al bloque de filas correspondiente del hilo i */
void aplicar_regla(FuncionRegla funcion, int i, board_t *board, int nuproc) {
    unsigned int height = board->height;
    unsigned int width = board->width;
    int filasXhilo = height/nuproc;
    if (i < nuproc - 1) {
        for (int r = filasXhilo * i; r < filasXhilo * (i+1); r++) {
            for (int c = 0; c < width; c++) {
                funcion(board, r, c);
            }
        }
    } else {
        for (int r = filasXhilo * i; r < height; r++) {
            for (int c = 0; c < width; c++) {
                funcion(board, r, c);
            }
        }
    }
}

/* Updatea los estados del bloque de filas correspondiente del hilo i */
void update(board_t *board, int i, int *state_thr, int nuproc){
	if (state_thr[i] == TO_UPDATE ){
		aplicar_regla(change_state, i , board, nuproc);
	}
    sem_wait(&board->mutex);
    state_thr[i] = UPDATED;
}

/* Chequea que todos los hilos hayan updateado, en caso contrario, el hilo se quedara esperando.
    Si todos updatearon, se actualizaran los valores de todo el tablero, se reseteara el estado de
    los hilos y se los liberara */
void check_update(board_t *board, int i, int *state_thr, int *contador, int nuproc) {
    if (all_updated(state_thr, nuproc)) {
        for (int j = 0; j < nuproc; j++) {
            aplicar_regla(change_val, j, board, nuproc);
        }
        contador[0] ++;
        for (int j = 0; j < nuproc; j++) {
            state_thr[j] = TO_UPDATE;
        }
        for (int j = 0; j < nuproc; j++) {
            sem_post(&board->sem[j]);
        }
    }
    sem_post(&board->mutex);
    sem_wait(&board->sem[i]);
}

/* Recibe los argumentos necesarios para poder aplicar las reglas cycles veces a su bloque
    de filas correspondiente */
void* vida(void* arg) {
    /* Inicializamos los argumentos */
    args_t *args = arg;
    int i = args->i;
    int cycles = args->cycles;
    int nuproc = args->nuproc;
    int *contador = args->contador;
    int *state_threads = args->state_threads;
    board_t *board = args->board;

    /* actualizamos el estado de hilo i a TO_UPDATE */
    state_threads[i] = TO_UPDATE;

    for ( ;contador[0] < cycles; ) {
        update(board, i, state_threads, nuproc);
        check_update(board, i, state_threads, contador, nuproc);
    }
}

board_t *congwayGoL(board_t *board, unsigned int cycles, int nuproc) {
    if (nuproc > board->height) {   
        nuproc = board->height; /* Si nuproc es mayor a la cantidad de filas, tomamos nuproc = filas */
    }
    pthread_t threads[nuproc];  /* arreglo con los hilos */
    int state_threads[nuproc];  /* arreglo con los estados de los hilos */

    args_t args[nuproc];        /* arreglo con los argumentos */
    int *contador = malloc(sizeof(int));
    contador[0] = 0;

    for (int i = 0; i < nuproc; i++) {  /* inicializamos args */
        args[i].board = board;
        args[i].contador = contador;
        args[i].cycles = cycles;
        args[i].nuproc = nuproc;
        args[i].state_threads = state_threads;
        args[i].i = i;
    }

    board->sem = malloc(sizeof(sem_t)*nuproc);  /* pedimos memoria para los semaforos */
    
    /* Inicializamos los semaforos */
    sem_init(&board->mutex, 0, 1);
    for (int i = 0; i < nuproc; i++) {
        sem_init(&board->sem[i], 0, 0);
    }

    /* Inicializamos los hilos */
    for (int i = 0; i < nuproc; i++) {
        if ((pthread_create( &threads[i]
                            , NULL
                            , vida
                            , (void* )&args[i])) != 0) {
            perror("Falló la creación de un hilo\n");
            exit(EXIT_FAILURE);
        }
    }

    /* Esperamos a que todos los hilos terminen */
    for (int i = 0; i < nuproc; i++) {
		if (pthread_join(threads[i] , NULL) != 0){
            perror("Falló la espera de un hilo\n");
            exit(EXIT_FAILURE);
        }
	}
    
    return board;   
}

/******************************************************************************/