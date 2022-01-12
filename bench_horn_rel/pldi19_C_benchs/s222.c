#include "declarations.h"

//	loop distribution
//	partial loop vectorizatio recurrence in middle

TYPE s222(int count) {
	for (int i = 1; i < count*8; i++) {
		a[i] += b[i] * c[i];
		e[i] = e[i - 1] * e[i - 1];
		a[i] -= b[i] * c[i];
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s222(count);
}


/*
TYPE s222(int count) {
	for (int i = 1; i < count*8; i++) {
		a[i] += b[i] * c[i];
		a[i] -= b[i] * c[i];
	}
	for (int i = 1; i < count*8; i++) {
		e[i] = e[i - 1] * e[i - 1];
	}
	return 0;
}
*/