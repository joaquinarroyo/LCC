#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>

void swap(int *num1, int *num2) {
    int tmp = num1[0];
    num1[0] = num2[0];
    num2[0] = tmp;
} 

int main(){
    int *num1 = malloc(sizeof(int));
    int *num2 = malloc(sizeof(int));
    num1[0] = 4;
    num2[0] = 5;
    swap(num1, num2);
    printf("%d, %d\n", num1[0], num2[0]);
    return 0;
}
