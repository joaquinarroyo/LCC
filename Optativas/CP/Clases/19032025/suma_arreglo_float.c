#include <omp.h>
#include <stdio.h>

#ifndef N
#define N (1L<<K)
#endif

float a[N];

int main(void)
{
	double t = omp_get_wtime();
	size_t i = 0L;
	float s = 0.0f;
	for (i=0L; i<N; ++i) {
		s = s+a[i];
	}
	printf("cels/µs: %lf\n", N / (1.0E6*(omp_get_wtime()-t)));
	printf("GiB/s: %lf\n", N*sizeof(a[0]) / ((1<<30)*(omp_get_wtime()-t)));


	return (int)s;
}
