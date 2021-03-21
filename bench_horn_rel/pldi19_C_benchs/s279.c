#include "declarations.h"


TYPE s279(int count) {
	for (int i = 0; i < count*8; i++) {
		if (a[i] > (float)0.) {
			goto L20;
		}
		b[i] = -b[i] + d[i] * d[i];
		if (b[i] <= a[i]) {
			goto L30;
		}
		c[i] += d[i] * e[i];
		goto L30;
L20:
		c[i] = -c[i] + e[i] * e[i];
L30:
		a[i] = b[i] + c[i] * d[i];
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s279(count);
}