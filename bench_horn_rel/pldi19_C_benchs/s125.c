#include "declarations.h"

//	induction variable recognition
//	induction variable in two loops; collapsing possible

TYPE s000(int count) {
	int k = -1;
	for (int i = 0; i < count; i++) {
		for (int j = 0; j < count; j++) {
			k++;
			array[k] = aa[i][j] + bb[i][j] * cc[i][j];
		}
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s000(count);
}