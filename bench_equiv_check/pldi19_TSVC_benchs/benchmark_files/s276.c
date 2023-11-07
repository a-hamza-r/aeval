#include "declarations.h"

//	control flow
//	if test using loop index

TYPE 
__attribute__((noinline))
s276(TYPE* a, TYPE* b, TYPE *c, TYPE *d, int count, int mid) {
	for (int i = 0; i < count*8; i++) {
		if (i+1 < mid) {
			a[i] += b[i] * c[i];
		} else {
			a[i] += b[i] * d[i];
		}
	}
	return 0;
}

TYPE 
__attribute__((noinline))
s276_vec(TYPE* a, TYPE* b, TYPE *c, TYPE *d, int count, int mid) {
	for (int i = 0; i < count*8; i+=8) {
		if (i+1 < mid) {
			a[i] += b[i] * c[i];
		} else {
			a[i] += b[i] * d[i];
		}

		if (i+1+1 < mid) {
			a[i+1] += b[i+1] * c[i+1];
		} else {
			a[i+1] += b[i+1] * d[i+1];
		}

		if (i+2+1 < mid) {
			a[i+2] += b[i+2] * c[i+2];
		} else {
			a[i+2] += b[i+2] * d[i+2];
		}

		if (i+3+1 < mid) {
			a[i+3] += b[i+3] * c[i+3];
		} else {
			a[i+3] += b[i+3] * d[i+3];
		}

		if (i+4+1 < mid) {
			a[i+4] += b[i+4] * c[i+4];
		} else {
			a[i+4] += b[i+4] * d[i+4];
		}

		if (i+5+1 < mid) {
			a[i+5] += b[i+5] * c[i+5];
		} else {
			a[i+5] += b[i+5] * d[i+5];
		}

		if (i+6+1 < mid) {
			a[i+6] += b[i+6] * c[i+6];
		} else {
			a[i+6] += b[i+6] * d[i+6];
		}

		if (i+7+1 < mid) {
			a[i+7] += b[i+7] * c[i+7];
		} else {
			a[i+7] += b[i+7] * d[i+7];
		}
	}
	return 0;
}

int main() {
	return 0;
}