// https://stackoverflow.com/questions/25622745/transpose-an-8x8-float-using-avx-avx2
// https://stackoverflow.com/questions/16941098/fast-memory-transpose-with-sse-avx-and-openmp

#include <stdio.h>
#include <x86intrin.h>
#include <omp.h>
#include <assert.h>

#ifndef L
#define L (1<<12)
#endif

#ifndef BL
#define BL (1<<6)
#endif

float a[L][L] __attribute__((aligned(64)));
float b[L][L] __attribute__((aligned(64)));


inline void tran_AVX_8x8(float* mat, float* matT) {
  __m256  r0, r1, r2, r3, r4, r5, r6, r7;
  __m256  t0, t1, t2, t3, t4, t5, t6, t7;

  r0 = _mm256_load_ps(&mat[0*L]);
  r1 = _mm256_load_ps(&mat[1*L]);
  r2 = _mm256_load_ps(&mat[2*L]);
  r3 = _mm256_load_ps(&mat[3*L]);
  r4 = _mm256_load_ps(&mat[4*L]);
  r5 = _mm256_load_ps(&mat[5*L]);
  r6 = _mm256_load_ps(&mat[6*L]);
  r7 = _mm256_load_ps(&mat[7*L]);

  t0 = _mm256_unpacklo_ps(r0, r1);
  t1 = _mm256_unpackhi_ps(r0, r1);
  t2 = _mm256_unpacklo_ps(r2, r3);
  t3 = _mm256_unpackhi_ps(r2, r3);
  t4 = _mm256_unpacklo_ps(r4, r5);
  t5 = _mm256_unpackhi_ps(r4, r5);
  t6 = _mm256_unpacklo_ps(r6, r7);
  t7 = _mm256_unpackhi_ps(r6, r7);

  r0 = _mm256_shuffle_ps(t0,t2,_MM_SHUFFLE(1,0,1,0));
  r1 = _mm256_shuffle_ps(t0,t2,_MM_SHUFFLE(3,2,3,2));
  r2 = _mm256_shuffle_ps(t1,t3,_MM_SHUFFLE(1,0,1,0));
  r3 = _mm256_shuffle_ps(t1,t3,_MM_SHUFFLE(3,2,3,2));
  r4 = _mm256_shuffle_ps(t4,t6,_MM_SHUFFLE(1,0,1,0));
  r5 = _mm256_shuffle_ps(t4,t6,_MM_SHUFFLE(3,2,3,2));
  r6 = _mm256_shuffle_ps(t5,t7,_MM_SHUFFLE(1,0,1,0));
  r7 = _mm256_shuffle_ps(t5,t7,_MM_SHUFFLE(3,2,3,2));

  t0 = _mm256_permute2f128_ps(r0, r4, 0x20);
  t1 = _mm256_permute2f128_ps(r1, r5, 0x20);
  t2 = _mm256_permute2f128_ps(r2, r6, 0x20);
  t3 = _mm256_permute2f128_ps(r3, r7, 0x20);
  t4 = _mm256_permute2f128_ps(r0, r4, 0x31);
  t5 = _mm256_permute2f128_ps(r1, r5, 0x31);
  t6 = _mm256_permute2f128_ps(r2, r6, 0x31);
  t7 = _mm256_permute2f128_ps(r3, r7, 0x31);

  _mm256_store_ps(&matT[0*L], t0);
  _mm256_store_ps(&matT[1*L], t1);
  _mm256_store_ps(&matT[2*L], t2);
  _mm256_store_ps(&matT[3*L], t3);
  _mm256_store_ps(&matT[4*L], t4);
  _mm256_store_ps(&matT[5*L], t5);
  _mm256_store_ps(&matT[6*L], t6);
  _mm256_store_ps(&matT[7*L], t7);
}

void tran_cache(float * mat, float * matT) {
	unsigned int i=0, j=0;
	for (i=0; i<BL; i+=8)
		for (j=0; j<BL; j+=8)
			tran_AVX_8x8(&mat[i*L+j], &matT[j*L+i]);
}

void tran_mem(float * mat, float * matT) {
	unsigned int i=0, j=0;
	for (i=0; i<L; i+=BL)
		for (j=0; j<L; j+=BL)
			tran_cache(&mat[i*L+j], &matT[j*L+i]);
}

/* B = A^t */
int main(void) {
	unsigned int i=0, j=0;
	assert(0==L%BL);
	assert(0==BL%8);
	// setup
	//for(i=0;i<L;++i) for(j=0;j<L;++j) a[i][j]=b[i][j]=(float)(i*L+j);
	// transpose
	tran_mem(&a[0][0], &b[0][0]);
	// test
	//for(i=0;i<L;++i) for(j=0;j<L;++j) assert(a[i][j]==b[j][i]);

	return (int)b[(int)b[0][2]][(int)b[2][0]];
}
