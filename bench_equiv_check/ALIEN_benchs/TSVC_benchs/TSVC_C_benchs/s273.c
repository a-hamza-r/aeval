#include "declarations.h"

//	control flow
//	simple loop with dependent conditional

TYPE s273(int count) {
	for (int i = 0; i < count*8; i++) {
		a[i] += d[i] * e[i];
		if (a[i] < (float)0.)
			b[i] += d[i] * e[i];
		c[i] += a[i] * d[i];
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s273(count);
}