#Makefile Cainelli Arroyo TP2

#CFLAGS indicara las banderas con la cual se van a compilar todos los archivos

CFLAGS = -g -Wall -Werror

#interprete compila el programa a utilizar, con sus dos dependencias incluidas

interprete: itree.o comandos.o
	gcc -o interprete interprete.c itree.o comandos.o $(CFLAGS)

itree.o: itree.c itree.h
	gcc -c itree.c $(CFLAGS)

comandos.o: itree.c comandos.c comandos.h
	gcc -c comandos.c itree.c $(CFLAGS)

#clean borra todos los archivos objeto creados

clean:
	rm *.o

