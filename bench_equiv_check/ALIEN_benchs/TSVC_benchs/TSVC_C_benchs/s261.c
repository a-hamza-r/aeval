#include "declarations.h"

//	scalar and array expansion
//	wrap-around scalar under an if

TYPE s261(int count) {
	int t;
	for (int i = 1; i < count*8; ++i) {
		t = a[i] + b[i];
		a[i] = t + c[i-1];
		t = c[i] * d[i];
		c[i] = t;
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s261(count);
}