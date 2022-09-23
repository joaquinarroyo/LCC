
simulador: gameDef.o board.o
	gcc -o simulador simulador.c gameDef.o board.o -pthread

gameDef.o: gameDef.c gameDef.h board.c board.h
	gcc -c gameDef.c board.c -pthread

board.o: board.c board.h
	gcc -c board.c -pthread

clean:
	rm *.o