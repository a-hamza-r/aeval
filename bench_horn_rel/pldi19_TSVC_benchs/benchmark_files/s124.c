#include "declarations.h"

//	induction variable recognition
//	induction variable under both sides of if (same value)

TYPE 
__attribute__((noinline))
s124(TYPE* a, TYPE* b, TYPE *c, TYPE *d, TYPE *e, int count) {
	for (int i = 0; i < count*8; i++) {
		if (b[i] > 0) {
			a[i] = b[i] + d[i] * e[i];
		} else {
			a[i] = c[i] + d[i] * e[i];
		}
	}
	return 0;
}

TYPE 
__attribute__((noinline))
s124_vec(TYPE* a, TYPE* b, TYPE *c, TYPE *d, TYPE *e, int count) {
	for (int i = 0; i < count*8; i+=8) {
		if (b[i] > 0) {
			a[i] = b[i] + d[i] * e[i];
		} else {
			a[i] = c[i] + d[i] * e[i];
		}

		if (b[i+1] > 0) {
			a[i+1] = b[i+1] + d[i+1] * e[i+1];
		} else {
			a[i+1] = c[i+1] + d[i+1] * e[i+1];
		}

		if (b[i+2] > 0) {
			a[i+2] = b[i+2] + d[i+2] * e[i+2];
		} else {
			a[i+2] = c[i+2] + d[i+2] * e[i+2];
		}

		if (b[i+3] > 0) {
			a[i+3] = b[i+3] + d[i+3] * e[i+3];
		} else {
			a[i+3] = c[i+3] + d[i+3] * e[i+3];
		}

		if (b[i+4] > 0) {
			a[i+4] = b[i+4] + d[i+4] * e[i+4];
		} else {
			a[i+4] = c[i+4] + d[i+4] * e[i+4];
		}

		if (b[i+5] > 0) {
			a[i+5] = b[i+5] + d[i+5] * e[i+5];
		} else {
			a[i+5] = c[i+5] + d[i+5] * e[i+5];
		}

		if (b[i+6] > 0) {
			a[i+6] = b[i+6] + d[i+6] * e[i+6];
		} else {
			a[i+6] = c[i+6] + d[i+6] * e[i+6];
		}

		if (b[i+7] > 0) {
			a[i+7] = b[i+7] + d[i+7] * e[i+7];
		} else {
			a[i+7] = c[i+7] + d[i+7] * e[i+7];
		}
	}
	return 0;
}

int main() {
	return 0;
}