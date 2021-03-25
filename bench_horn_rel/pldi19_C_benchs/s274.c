#include "declarations.h"

//	control flow
//	complex loop with dependent conditional

TYPE s274(int count) {
	for (int i = 0; i < LEN; i++) {
		a[i] = c[i] + e[i] * d[i];
		if (a[i] > (float)0.) {
			b[i] = a[i] + b[i];
		} else {
			a[i] = d[i] * e[i];
		}
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s274(count);
}