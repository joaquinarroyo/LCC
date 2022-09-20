#include <stdio.h>

int main(){
    long int a = 0xAA;
    long int b = a | (a << 24);
    printf("%d\n",b == 2852126890);
}