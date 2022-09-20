#include <stdio.h>
#include <stdlib.h>

/*
 * Ej 2
 * El programa recibe como argumento tres numeros a, b y c, y rota sus valores sin utilizar
 * variables auxiliares.
 * a -> b -> c -> a
*/
int main(int argc, char* argv[]){
    int a = atoi(argv[1]);
    int b = atoi(argv[2]);
    int c = atoi(argv[3]);
    printf("%d %d %d\n", a, b, c);
    a = a^b;
    b = a^b;
    a = a^b;
    // a y b rotados
    a = a^c;
    c = a^c;
    a = a^c;
    // a(que contiene b) y c rotados
    printf("%d %d %d\n", a,b,c);
    return 0;
}