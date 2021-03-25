#include "declarations.h"

//	control flow
//	if/goto to block if-then-else

TYPE s278(int count) {
	for (int i = 0; i < count*8; i++) {
		if (a[i] > (float)0.) {
			goto L20;
		}
		b[i] = -b[i] + d[i] * e[i];
		goto L30;
L20:
		c[i] = -c[i] + d[i] * e[i];
L30:
		a[i] = b[i] + c[i] * d[i];
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s278(count);
}