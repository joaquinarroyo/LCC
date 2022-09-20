#include <stdio.h>

int main(){
    int a = 5;
    a = a << 8;
    int b = 1280; // =  00000000 00000000 00000101 00000000
    printf("%d\n", a == b);
}