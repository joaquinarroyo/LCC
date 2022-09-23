
semaforo: stack.o
	gcc -o semaforo semaforos.c stack.o  -pthread

stack.o: stack.c stack.h
	gcc -c stack.c

clean:
	rm *.o