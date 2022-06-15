#include "declarations.h"

//	control loops
//	vector dot product reduction

TYPE 
__attribute__((noinline))
s152(TYPE* a, TYPE* b, TYPE *c, TYPE *d, TYPE *e, int count) {
	for (int i = 0; i < count*8; i++) {
		b[i] = d[i] * e[i];
		a[i] += b[i] * c[i];
	}
  return 0;
}

TYPE 
__attribute__((noinline))
s152_vec(TYPE* a, TYPE* b, TYPE *c, TYPE *d, TYPE *e, int count) {
	for (int i = 0; i < count*8; i+=8) {
		b[i] = d[i] * e[i];
		a[i] += b[i] * c[i];

		b[i+1] = d[i+1] * e[i+1];
		a[i+1] += b[i+1] * c[i+1];

		b[i+2] = d[i+2] * e[i+2];
		a[i+2] += b[i+2] * c[i+2];

		b[i+3] = d[i+3] * e[i+3];
		a[i+3] += b[i+3] * c[i+3];

		b[i+4] = d[i+4] * e[i+4];
		a[i+4] += b[i+4] * c[i+4];

		b[i+5] = d[i+5] * e[i+5];
		a[i+5] += b[i+5] * c[i+5];

		b[i+6] = d[i+6] * e[i+6];
		a[i+6] += b[i+6] * c[i+6];

		b[i+7] = d[i+7] * e[i+7];
		a[i+7] += b[i+7] * c[i+7];
	}
  return 0;
}

int main() {
	return 0;
}