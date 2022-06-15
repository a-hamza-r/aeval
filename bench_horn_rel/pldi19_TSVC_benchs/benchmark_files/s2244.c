#include "declarations.h"

//	node splitting
//	cycle with true and anti dependency

TYPE 
__attribute__((noinline))
s2244(TYPE* a, TYPE* b, TYPE *c, TYPE *e, int count) {
	for (int i = 0; i < count*8-1; i++) {
		a[i+1] = b[i] + e[i];
		a[i] = b[i] + c[i];
	}
  return 0;
}

TYPE 
__attribute__((noinline))
s2244_vec(TYPE* a, TYPE* b, TYPE *c, TYPE *e, int count) {
	if (count > 0) {
	a[0+1] = b[0] + e[0];
	a[0] = b[0] + c[0];

	a[0+1+1] = b[0+1] + e[0+1];
	a[0+1] = b[0+1] + c[0+1];

	a[0+2+1] = b[0+2] + e[0+2];
	a[0+2] = b[0+2] + c[0+2];

	a[0+3+1] = b[0+3] + e[0+3];
	a[0+3] = b[0+3] + c[0+3];

	a[0+4+1] = b[0+4] + e[0+4];
	a[0+4] = b[0+4] + c[0+4];

	a[0+5+1] = b[0+5] + e[0+5];
	a[0+5] = b[0+5] + c[0+5];

	a[0+6+1] = b[0+6] + e[0+6];
	a[0+6] = b[0+6] + c[0+6];
}

	for (int i = 7; i < count*8-1; i+=8) {
		a[i+1] = b[i] + e[i];
		a[i] = b[i] + c[i];

		a[i+1+1] = b[i+1] + e[i+1];
		a[i+1] = b[i+1] + c[i+1];

		a[i+2+1] = b[i+2] + e[i+2];
		a[i+2] = b[i+2] + c[i+2];

		a[i+3+1] = b[i+3] + e[i+3];
		a[i+3] = b[i+3] + c[i+3];

		a[i+4+1] = b[i+4] + e[i+4];
		a[i+4] = b[i+4] + c[i+4];

		a[i+5+1] = b[i+5] + e[i+5];
		a[i+5] = b[i+5] + c[i+5];

		a[i+6+1] = b[i+6] + e[i+6];
		a[i+6] = b[i+6] + c[i+6];

		a[i+7+1] = b[i+7] + e[i+7];
		a[i+7] = b[i+7] + c[i+7];
	}
  return 0;
}

int main() {
	return 0;
}