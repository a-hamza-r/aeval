#include "declarations.h"

//	control flow
//	if test using loop index

TYPE s276(int count) {
	for (int i = 0; i < count*8; i++) {
		if (i+1 < mid) {
			a[i] += b[i] * c[i];
		} else {
			a[i] += b[i] * d[i];
		}
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s276(count);
}