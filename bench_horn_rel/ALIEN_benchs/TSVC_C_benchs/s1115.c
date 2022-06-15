#include "declarations.h"

//	linear dependence testing
//	triangular saxpy loop

TYPE s1115(int count) {
	for (int i = 0; i < count*8; i++) {
		for (int j = 0; j < count*8; j++) {
			aa[i][j] = aa[i][j]*cc[j][i] + bb[i][j];
		}
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s1115(count);
}