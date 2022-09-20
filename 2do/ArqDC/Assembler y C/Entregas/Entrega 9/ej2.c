#include <stdint.h>
#include <stdio.h>
#include <math.h>

// 1)

#define MANTISA_LARGO 23
#define EXPONENTE_LARGO 8
#define UNINT(f) (*(const uint32_t*)&(f))
#define SESGO ((1<<(EXPONENTE_LARGO - 1))-1)
#define MASCARA(ancho) ((1<<(ancho))-1)

int exponente(float n){
    return (int)((UNINT(n) >> MANTISA_LARGO) & MASCARA(EXPONENTE_LARGO)) - SESGO;
}

int fraccion(float n){
    return (int)(UNINT(n) & MASCARA(MANTISA_LARGO));
}

// 2)

int myisnan(float n){
    if (fraccion(n) != 0 && exponente(n) == 128){
        return 1;
    } else {
        return 0;
    }
}

int myisnan2(float n){
    if (n != n){
        return 1;
    } else {
        return 0;
    }
}

int main(void) {
    float g = 0.0;
    float f = 1.0 / g;
    printf("f: %f\n", f);
    if (isnan(f)) {
        printf("isnan dice que si\n");
    }
    if (myisnan(f)) {
        printf("myisnan dice que si\n");
    }
    if (myisnan2(f)) {
        printf("myisnan2 dice que si\n");
    }
    return 0;
}

// Inf es tomado distinto de Nan, por lo tanto nuestras funciones retornarian 0.
// Si se suma un valor a inf este sigue siendo inf.


