#include "declarations.h"


TYPE s123(int count) {
	int j = -1;
	for (int i = 0; i < count*4; i++) {
		j++;
		a[j] = b[i] + d[i] * e[i];
		if (c[i] > (float)0.) {
			j++;
			a[j] = c[i] + d[i] * e[i];
		}
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s123(count);
}