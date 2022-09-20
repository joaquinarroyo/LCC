#include <stdio.h>

int main(){
    long int a = 2147516416; // =  10000000 00000000 10000000 00000000
    long int b = 1;
    long int c = 1;
    b = b << 31;
    c = c << 15;
    long int d = b | c;
    printf("%d\n", a == d);
    return 0;
}