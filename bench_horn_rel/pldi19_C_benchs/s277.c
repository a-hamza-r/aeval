#include "declarations.h"


TYPE s277(int count) {
	for (int i = 0; i < count*8-1; i++) {
		if (a[i] >= (float)0.) {
			goto L20;
		}
		if (b[i] >= (float)0.) {
			goto L30;
		}
		a[i] += c[i] * d[i];
L30:
		b[i+1] = c[i] + d[i] * e[i];
L20:
;
		
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s277(count);
}