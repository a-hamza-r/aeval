#include "declarations.h"

//	induction variable recognition
//	induction variable in two loops; recurrence in inner loop

TYPE s126(int count) {
	int k = 1;
	for (int i = 0; i < count*8; i++) {
		for (int j = 1; j < count*8; j++) {
			bb[j][i] = bb[j-1][i] + array[k-1] * cc[j][i];
			++k;
		}
		++k;
	}
	return 0;
}

/*
// after induction variable recognition
TYPE s126(int count) {
	for (int j = 1; j < count*8; j++) {
		for (int i = 0; i < count*8; i++) {
			bb[j][i] = bb[j-1][i] + array[i+j-1] * cc[j][i];
		}
	}
	return 0;
}
*/

int nondet();

int main() {
	int count = nondet();
	s126(count);
}