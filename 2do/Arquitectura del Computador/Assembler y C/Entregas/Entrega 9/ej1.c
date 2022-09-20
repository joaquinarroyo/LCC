#include <stdint.h>
#include <stdio.h>

#define MANTISA_LARGO 23
#define EXPONENTE_LARGO 8
#define UNINT(f) (*(const uint32_t*)&(f))
#define SESGO ((1<<(EXPONENTE_LARGO - 1))-1)
#define MASCARA(ancho) ((1<<(ancho))-1)
#define UNOIMPLICITO (1<<MANTISA_LARGO)

int fraccion(float n){
    return (int)((UNINT(n) >> MANTISA_LARGO) & MASCARA(EXPONENTE_LARGO)) - SESGO;
}

int exponente(float n){
    return (int)(UNINT(n) & MASCARA(MANTISA_LARGO)) | UNOIMPLICITO;
}


int main(){
    float numero = 7.25;
    printf("%d\n",exponente(numero));
    printf("%d\n",fraccion(numero));
}