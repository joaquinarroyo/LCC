#Makefile Arroyo TPFinal
#CFLAGS indicara las banderas con la cual se van a compilar todos los archivos

CFLAGS = -g -Wall -Werror

#interprete compila el programa a utilizar, con sus dos dependencias incluidas

interprete: conjuntos.o comandos.o
	gcc -o interprete interprete.c conjuntos.o comandos.o $(CFLAGS)

conjuntos.o: conjuntos.c conjuntos.h
	gcc -c conjuntos.c $(CFLAGS)

comandos.o: comandos.c comandos.h conjuntos.h
	gcc -c comandos.c $(CFLAGS)

#clean borra todos los archivos objeto creados

clean:
	rm *.o

