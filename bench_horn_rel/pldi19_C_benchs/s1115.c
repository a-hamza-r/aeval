#include "declarations.h"

//	linear dependence testing
//	triangular saxpy loop

TYPE s1115(int count) {
	for (int i = 0; i < count; i++) {
		for (int j = 0; j < count; j++) {
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