servidor: comandos.o
	gcc -o servidor servidor.c comandos.o -pthread

cliente: cliente.c
	gcc -o cliente cliente.c -pthread

comandos.o: comandos.c comandos.h
	gcc -c comandos.c 

clean:
	rm *.o
	rm servidor
	rm cliente