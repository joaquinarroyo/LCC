#include <stdio.h>

int ack(int i, int j) {
    if (i == 0) {
        return j + 1;
    } else if (j == 0) {
        return ack(i - 1, 1);
    } else {
        return ack(i - 1, ack(i, j - 1));
    }
}

int main() {
    int i = 3;
    int j = 11;
    int result = ack(i, j);
    printf("ack %d %d = %d\n", i, j, result);
    return 0;
}
