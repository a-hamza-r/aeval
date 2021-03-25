#include "declarations.h"

//	diagonals
//	identity matrix, best results vectorize both inner and outer loops

TYPE s2102(int count) {
	for (int i = 0; i < count; i++) {
		for (int j = 0; j < count; j++) {
			aa[j][i] = (float)0.;
		}
		aa[i][i] = (float)1.;
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s2102(count);
}