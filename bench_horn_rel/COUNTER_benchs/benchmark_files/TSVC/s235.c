#include "declarations.h"

//	loop interchanging
//	imperfectly nested loops

TYPE s235(int count) {
	for (int i = 0; i < count*8; i++) {
		a[i] += b[i] * c[i];
		for (int j = 1; j < count*8; j++) {
			aa[j][i] = aa[j-1][i] + bb[j][i] * a[i];
		}
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s235(count);
}