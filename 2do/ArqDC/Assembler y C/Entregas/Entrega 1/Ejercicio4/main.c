#include <stdio.h>
#include <stdlib.h>

/*
 * Ej 4
 * El programa recibe como argumento el numero a imprimir en binario.
*/

int is_one(unsigned long n, int b){
    //Calcula si el bit b es 1 o 0 a partir de una mascara.
    long mascara = 1<<(b-1);
    long res = (n-1) & mascara;
    return res>>(b-1);
}

void printbin(unsigned long n){
    //A partir de la funcion is_one calcula el valor de cada bit del numero n y lo imprime.
    for(int i = 63; i >= 0; i--){
        printf("%d",is_one(n,i));
    }
    printf("\n");
}

int main(int argc, char* argv[]){
    long n = atoll(argv[1]);
    printbin(n);
    return 0;
}