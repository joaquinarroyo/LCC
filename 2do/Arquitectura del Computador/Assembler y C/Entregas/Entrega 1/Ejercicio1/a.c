#include <stdio.h>

int main(){
    long a = 2147483648; // = 10000000 00000000 00000000 00000000
    long b = 1;
    b = b<<31;
    printf("%d\n",a == b);
    return 0;
}
