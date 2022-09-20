#include <stdio.h>
#include <stdlib.h>

/*
 * Ej 3
 * El programa recibe como argumento el numero y la posicion del bit para calcular si es 1 o 0.
*/

int is_one(unsigned long n, int b){
    //Calcula si el bit b es 1 o 0 a partir de una mascara.
    unsigned long mascara = 1<<(b-1);
    unsigned long res = (n-1) & mascara;
    return res>>(b-1);
}

int main(int argc, char* argv[]){
    unsigned long a = atoll(argv[1]);
    int bit = atoi(argv[2]);
    printf("%d\n",is_one(a,bit));
    return 0;
}