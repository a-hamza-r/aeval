#include "declarations.h"


TYPE s211(int count) {
	for (int i = 1; i < count*8-1; i++) {
		a[i] = b[i - 1] + c[i] * d[i];
		b[i] = b[i + 1] - e[i] * d[i];
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s211(count);
}