#include "declarations.h"

//	control flow
//	tests for recognition of loop independent dependences
//	between statements in mutually exclusive regions.

TYPE s161(int count) {
	for (int i = 0; i < count*8-1; ++i) {
		if (b[i] < (float)0.) {
			goto L20;
		}
		a[i] = c[i] + d[i] * e[i];
		goto L10;
L20:
		c[i+1] = a[i] + d[i] * d[i];
L10:
			;
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s161(count);
}