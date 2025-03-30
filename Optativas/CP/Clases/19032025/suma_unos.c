#ifndef N
#define N 2048
#endif

#include <stdio.h>

// static de nuevo o no hace miracle optimizations!
// https://stackoverflow.com/questions/47202557/what-is-a-designated-initializer-in-c
static int a[N]={[0 ... N-1] = 1};

int main(void)
{
	int i = 0;
	int s = 0;
	for (i=0; i<N; ++i) {
		s=s+a[i];
	}

	return s;
}
