#include "declarations.h"

//	induction variable recognition
//	induction variable under both sides of if (same value)

TYPE s124(int count) {
	int j = -1;
	for (int i = 0; i < count*8; i++) {
		if (b[i] > (float)0.) {
			j++;
			a[j] = b[i] + d[i] * e[i];
		} else {
			j++;
			a[j] = c[i] + d[i] * e[i];
		}
	}
	return 0;
}


/*after induction variable recognition:

TYPE s124(int count) {
	for (int i = 0; i < count*8; i++) {
		if (b[i] > (float)0.) {
			a[i] = b[i] + d[i] * e[i];
		} else {
			a[i] = c[i] + d[i] * e[i];
		}
	}
	return 0;
}
*/


int nondet();

int main() {
	int count = nondet();
	s124(count);
}