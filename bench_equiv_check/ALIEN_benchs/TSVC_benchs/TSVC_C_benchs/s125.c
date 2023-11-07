#include "declarations.h"

//	induction variable recognition
//	induction variable in two loops; collapsing possible

TYPE s125(int count) {
	int k = -1;
	for (int i = 0; i < count*8; i++) {
		for (int j = 0; j < count*8; j++) {
			k++;
			array[k] = aa[i][j] + bb[i][j] * cc[i][j];
		}
	}
	return 0;
}


// after induction variable recognition
TYPE s125(int count) {
	for (int i = 0; i < count*8; i++) {
		for (int j = 0; j < count*8; j++) {
			array[i*count+j] = aa[i][j] + bb[i][j] * cc[i][j];
		}
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s125(count);
}