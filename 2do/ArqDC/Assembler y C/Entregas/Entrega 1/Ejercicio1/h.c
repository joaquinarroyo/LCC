#include <stdio.h>

int main(){
    long int a = 0x80000000;
    long int b = -a;
    long int c = a + b;
    printf("%d\n",c == 0);
    return 0;
}