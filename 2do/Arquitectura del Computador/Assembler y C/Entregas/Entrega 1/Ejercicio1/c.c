#include <stdio.h>

int main(){
    long int a = 4294967040; // = 11111111 11111111 11111111 00000000
    long int b = -1;
    long int c = a & b;
    printf("%d\n", a == c);
}