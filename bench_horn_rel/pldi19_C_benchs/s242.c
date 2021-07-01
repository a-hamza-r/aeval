#include "declarations.h"

//	node splitting

TYPE s242(int count, int s1, int s2) {
	for (int i = 1; i < count*8; ++i) {
		a[i] = a[i - 1] + s1 + s2 + b[i] + c[i] + d[i];
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	int s1 = nondet();
	int s2 = nondet();
	s242(count, s1, s2);
}