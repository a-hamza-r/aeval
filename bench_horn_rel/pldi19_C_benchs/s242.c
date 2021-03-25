#include "declarations.h"

//	node splitting

TYPE s242(int count) {
	for (int i = 1; i < count*8; ++i) {
		a[i] = a[i - 1] + s1 + s2 + b[i] + c[i] + d[i];
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s242(count);
}