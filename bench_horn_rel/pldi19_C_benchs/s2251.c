#include "declarations.h"

//	scalar and array expansion
//	scalar expansion

TYPE s2251(int count) {
	float s = (float)0.0;
	for (int i = 0; i < count*8; i++) {
		a[i] = s*e[i];
		s = b[i]+c[i];
		b[i] = a[i]+d[i];
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s2251(count);
}