#include "declarations.h"

//	control flow
//	vector if/gotos

TYPE s1279(int count) {
	for (int i = 0; i < count*8; i++) {
		if (a[i] < (float)0.) {
			if (b[i] > a[i]) {
				c[i] += d[i] * e[i];
			}
		}
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s1279(count);
}