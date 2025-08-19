// Ejercicio 6a
#include "syscall.h"

static inline unsigned
strlen(const char *s ) {
    unsigned i;
    for(i=0; s[i]!='\0'; i++);
    return i;
}

static inline int
puts2(const char *s ) {
    unsigned len = strlen(s);
    return Write(s, len, CONSOLE_OUTPUT);
}

static inline void
itoa(int n, char *str) {
    int isNegative = 0;
    if (n < 0) {
        isNegative = 1;
        n = -n;
    }

    int length = 0;
    do {
        str[length++] = (n % 10) + '0';
        n /= 10;
    } while (n > 0);

    if (isNegative) {
        str[length++] = '-';
    }

    str[length] = '\0';

    // Reverse the string
    for (int i = 0, j = length - 1; i < j; i++, j--) {
        char temp = str[i];
        str[i] = str[j];
        str[j] = temp;
    }
}

static inline void
mystrcpy(char *dst, const char *src, int n) {
    int i = 0;
    while (i < n-1 && src[i] != '\0') {
        dst[i] = src[i];
        i++;
    }
    dst[i] = '\0';
}

static inline void
mystrcat(char *dst, const char *src, int n) {
    int i = 0;
    while (dst[i] != '\0' && i < n-1) i++;
    int j = 0;
    while (i < n-1 && src[j] != '\0') {
        dst[i++] = src[j++];
    }
    dst[i] = '\0';
}

static inline int
mystrcmp(const char *a, const char *b) {
    int i = 0;
    while (a[i] != '\0' && b[i] != '\0') {
        if (a[i] != b[i]) return a[i] - b[i];
        i++;
    }
    return a[i] - b[i];
}