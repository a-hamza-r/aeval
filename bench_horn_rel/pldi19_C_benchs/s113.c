#include "declarations.h"


TYPE s113(int count) {
	for (int i = 1; i < count*8; i++) {
		a[i] = a[0] + b[i];
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s113(count);
}