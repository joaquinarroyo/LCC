/* B = A^t */

#include <assert.h>

#ifndef L
#define L (1<<12)
#endif

#ifndef X
#define X 4
#endif

#ifndef Y
#define Y 4
#endif

const unsigned int BX=1<<X;
const unsigned int BY=1<<Y;

float a[L][L], b[L][L];

int main(void) {
	unsigned int i=0, j=0, k=0, l=0;
	assert(0==L%BX && 0==L%BY);
	for (i=0; i<L; i+=BY)
		for (j=0; j<L; j+=BX)
			for (k=i; k<i+BY; ++k)
				for (l=j; l<j+BX; ++l)
					b[l][k] = a[k][l];
	return (int)b[(int)b[0][2]][(int)b[2][0]];
}
