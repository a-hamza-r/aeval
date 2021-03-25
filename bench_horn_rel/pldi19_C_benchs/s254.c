#include "declarations.h"

//	scalar and array expansion
//	carry around variable

TYPE s254(int count) {
	x = b[count*8-1];
	for (int i = 0; i < count*8; i++) {
		a[i] = (b[i] + x) * (float).5;
		x = b[i];
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s254(count);
}