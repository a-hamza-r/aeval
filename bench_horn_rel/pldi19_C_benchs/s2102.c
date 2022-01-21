#include "declarations.h"

//	diagonals
//	identity matrix, best results vectorize both inner and outer loops

TYPE s2102(int count) {
	for (int i = 0; i < count*8; i++) {
		for (int j = 0; j < count*8; j++) {
			aa[j][i] = 0;
		}
		aa[i][i] = 1;
	}
  return 0;
}

/*
// after interchanging loops
TYPE s2102(int count) {
	for (int j = 0; j < count*8; j++) {
		for (int i = 0; i < count*8; i++) {
			aa[j][i] = 0;
		}
		aa[j][j] = 1;
	}
  return 0;
}
*/

int nondet();

int main() {
	int count = nondet();
	s2102(count);
}