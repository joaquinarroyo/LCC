#Makefile Cainelli Arroyo TP1

#CFLAGS indicara las banderas con la cual se van a compilar todos los archivos

CFLAGS = -g -Wall -Werror

#generador compilara el primer programa a entregar, llamando a todas sus dependencias

generador: input.o output.o persona.o GList.o
	gcc -o generador generador.c input.o output.o persona.o GList.o $(CFLAGS)

#ordenador compilara el segundo programa a entregar, llamando a todas sus dependencias

ordenador: input.o output.o persona.o GList.o
	gcc -o ordenador ordenador.c input.o output.o persona.o GList.o $(CFLAGS)

input.o: input.c input.h persona.c GList.c
	gcc -c input.c GList.c persona.c $(CFLAGS)

output.o: output.c output.h persona.c
	gcc -c output.c persona.c -Wno-multichar -Wno-overflow $(CFLAGS)

persona.o: persona.c persona.h
	gcc -c persona.c $(CFLAGS)

GList.o: GList.c GList.h
	gcc -c GList.c $(CFLAGS)

#clean borra todos los archivos objeto creados

clean:
	rm *.o

