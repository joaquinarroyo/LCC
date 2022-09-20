#include <stdio.h>
#include "guindows.h"

task t1, t2, t3, taskmain;

void ft1(){
	double d;
	for(d=-1;;d+=0.001) {
		printf("d=%f\n", d);
		TRANSFER(t1,t2);
	}
}

void ft2(){
	int i;
	for(i=0;i<10000;i++) {
		printf("i=%d\n", i);
		TRANSFER(t2,t3);
	}
	TRANSFER(t2, taskmain);
}

void ft3(){
	for (unsigned i = 0; i < 5000; i++) {
		printf("i=%u\n", i);
		TRANSFER(t3, t1);
	}
	TRANSFER(t3, taskmain);
}

int main(){
	stack(t1,ft1);
	stack(t2,ft2);
	stack(t3,ft3);
	TRANSFER(taskmain,t1);
	return 0;
}
