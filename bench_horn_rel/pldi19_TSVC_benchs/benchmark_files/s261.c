#include "declarations.h"

//	scalar and array expansion
//	wrap-around scalar under an if

TYPE 
__attribute__((noinline))
s261(TYPE* a, TYPE* b, TYPE *c, TYPE *d, int count) {
	int t;
	for (int i = 1; i < count*8; ++i) {
		t = a[i] + b[i];
		a[i] = t + c[i-1];
		t = c[i] * d[i];
		c[i] = t;
	}
	return 0;
}

TYPE 
__attribute__((noinline))
s261_vec(TYPE* a, TYPE* b, TYPE *c, TYPE *d, int count) {
	int t;
	if (count > 0) {
	t = a[1] + b[1];
	a[1] = t + c[1-1];
	t = c[1] * d[1];
	c[1] = t;

	t = a[1+1] + b[1+1];
	a[1+1] = t + c[1+1-1];
	t = c[1+1] * d[1+1];
	c[1+1] = t;

	t = a[1+2] + b[1+2];
	a[1+2] = t + c[1+2-1];
	t = c[1+2] * d[1+2];
	c[1+2] = t;

	t = a[1+3] + b[1+3];
	a[1+3] = t + c[1+3-1];
	t = c[1+3] * d[1+3];
	c[1+3] = t;

	t = a[1+4] + b[1+4];
	a[1+4] = t + c[1+4-1];
	t = c[1+4] * d[1+4];
	c[1+4] = t;

	t = a[1+5] + b[1+5];
	a[1+5] = t + c[1+5-1];
	t = c[1+5] * d[1+5];
	c[1+5] = t;

	t = a[1+6] + b[1+6];
	a[1+6] = t + c[1+6-1];
	t = c[1+6] * d[1+6];
	c[1+6] = t;
}
	for (int i = 8; i < count*8; i+=8) {
		t = a[i] + b[i];
		a[i] = t + c[i-1];
		t = c[i] * d[i];
		c[i] = t;

		t = a[i+1] + b[i+1];
		a[i+1] = t + c[i+1-1];
		t = c[i+1] * d[i+1];
		c[i+1] = t;

		t = a[i+2] + b[i+2];
		a[i+2] = t + c[i+2-1];
		t = c[i+2] * d[i+2];
		c[i+2] = t;

		t = a[i+3] + b[i+3];
		a[i+3] = t + c[i+3-1];
		t = c[i+3] * d[i+3];
		c[i+3] = t;

		t = a[i+4] + b[i+4];
		a[i+4] = t + c[i+4-1];
		t = c[i+4] * d[i+4];
		c[i+4] = t;

		t = a[i+5] + b[i+5];
		a[i+5] = t + c[i+5-1];
		t = c[i+5] * d[i+5];
		c[i+5] = t;

		t = a[i+6] + b[i+6];
		a[i+6] = t + c[i+6-1];
		t = c[i+6] * d[i+6];
		c[i+6] = t;

		t = a[i+7] + b[i+7];
		a[i+7] = t + c[i+7-1];
		t = c[i+7] * d[i+7];
		c[i+7] = t;
	}
	return 0;
}

int main() {
	return 0;
}