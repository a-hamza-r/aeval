#include "declarations.h"

//	linear dependence testing
//	no dependence - vectorizable

TYPE s1119(int count) {
	for (int i = 1; i < count*8; i++) {
		for (int j = 0; j < count*8; j++) {
			aa[i][j] = aa[i-1][j] + bb[i][j];
		}
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s1119(count);
}