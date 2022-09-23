#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <math.h>
#include <pthread.h>

typedef struct _Punto {
  double x;
  double y;
} punto;

int sq_aleatorios(int NPuntos, int ladoCuadrado, punto centro){
    int puntos = 0;
    for (int i = 0; i < NPuntos; i++){
        double x = drand48() * ladoCuadrado;
        double y = drand48() * ladoCuadrado;
        double d = sqrt(pow((x - centro.x), 2) + pow((y - centro.y), 2));
        if (d <= (centro.x)) {
            puntos ++;
        }
    }
    return puntos;
}

int main(int argc, char** argv){
    int NPuntos = atoi(argv[1]);
    float radio = atoi(argv[2]);
    float ladoCuadrado = radio*2;
    punto centro;
    centro.x = radio;
    centro.y = radio;
    int puntos = sq_aleatorios(NPuntos, ladoCuadrado ,centro);
    double pi = (4.0 * puntos) / NPuntos;
    printf("%d, %d\n", puntos, NPuntos);
    printf("Aproximacion de pi = %f\n", pi);
    return 0;
}