#include "declarations.h"


TYPE s272(int count) {
	for (int i = 0; i < count*8; i++) {
		if (e[i] >= t) {
			a[i] += c[i] * d[i];
			b[i] += c[i] * c[i];
		}
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s272(count);
}