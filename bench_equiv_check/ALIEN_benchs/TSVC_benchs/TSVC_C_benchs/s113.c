#include "declarations.h"

//	linear dependence testing
//	a(i)=a(1) but no actual dependence cycle

TYPE s113(int count) {
	for (int i = 1; i < count*8; i++) {
		a[i] = a[0] + b[i];
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s113(count);
}