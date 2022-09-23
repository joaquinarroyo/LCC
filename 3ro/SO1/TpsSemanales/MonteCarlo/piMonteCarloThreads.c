#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <math.h>
#include <pthread.h>
#define RADIO 5
#define NPUNTOS 10000000
#define NTHREADS 500
#define OPERACIONESTHREAD NPUNTOS/NTHREADS

typedef struct _Punto {
  double x;
  double y;
} punto;

void* sq_aleatorios(void* puntos){
    int* puntosCirc = puntos;

    punto centro;
    centro.x = RADIO;
    centro.y = RADIO;
    float ladoCuadrado = RADIO*2;

    for (int i = 0; i < OPERACIONESTHREAD; i++){
        double x = drand48() * ladoCuadrado;
        double y = drand48() * ladoCuadrado;
        double d = sqrt(pow((x - centro.x), 2) + pow((y - centro.y), 2));
        if (d <= (centro.x)) {
            puntosCirc[0]++;
        }
    }
}

int main(){
    pthread_t ths[NTHREADS];
    int* args = malloc(sizeof(int)*NTHREADS);
    

    /* Crear NTHREADS hilos */
    for (int i = 0; i < NTHREADS; i++) {
        args[i] = 0;
        if (pthread_create( &ths[i]
                            , NULL
                            , sq_aleatorios
                            , (void *)(&args[i]))
            != 0) {
            perror("Falló la creación de un hilo");
            exit(EXIT_FAILURE);
        }
    }

	/* Esperamos a que todos los threads terminen */
	for (int i = 0; i < NTHREADS; i++) {
		if (pthread_join(ths[i] , NULL) != 0){
            perror("Falló la espera de un hilo");
            exit(EXIT_FAILURE);
        }
	}

    int puntos;
    for (int i = 0; i < NTHREADS; i++) {
        puntos += args[i];
	}

    double pi = (4.0 * puntos) / NPUNTOS;
    printf("Aproximacion de pi = %lf\n", pi);
    return 0;
}