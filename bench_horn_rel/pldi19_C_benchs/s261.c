#include "declarations.h"


TYPE s261(int count) {
	for (int i = 1; i < count; ++i) {
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