#include "declarations.h"


TYPE s131(int count) {
	int m = 1;
	for (int i = 0; i < count*8 - 1; i++) {
		a[i] = a[i + m] + b[i];
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s131(count);
}