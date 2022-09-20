#include <stdio.h>

int main(){
    long int a = -1;
    long int b = ~(1<<8);
    long int c = a & b;
    printf("%d\n",c == -257);
    return 0;
}