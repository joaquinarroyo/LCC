#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define CHAR_MAX 80

/*
 * Ej 5
 * El programa recibe como argumento el codigo para codificar el string pedido
 * por consola.
*/

int main(int argc, char* argv[]){
    int codigo = atoi(argv[1]);
    char entrada[CHAR_MAX];
    scanf("%s",entrada);
    int entradaLong = strlen(entrada);
    printf("Palabra codificada: ");
    for(int i = 0; i < entradaLong; i++){
        int salida = entrada[i]^codigo;
        printf("%d ", salida);
    }
    printf("\n");
    return 0;
}

/*
 *  Para que el programa decodifique deberiamos aplicar a cada codigo obtenido con la operacion 
 *  codigoPrincipal XOR string[i],  la operacion codigo XOR codigoPrincipal, para asi obtener el codigo ASCII de cada
 *  caracter para poder imprimirlos. Es decir, hacer el proceso inverso al que se hace para codificar en este programa.
 *  No se gana nada codificando mas de una vez, es mas, se va alternando entre el string normal y el string codificado.
*/
