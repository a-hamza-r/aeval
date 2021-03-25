#include "declarations.h"

//	loop interchange
//	interchanging of triangular loops

TYPE s232(int count) {
	for (int j = 1; j < LEN2; j++) {
		for (int i = 1; i <= j; i++) {
			aa[j][i] = aa[j][i-1]*aa[j][i-1]+bb[j][i];
		}
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s232(count);
}