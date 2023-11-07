#include "declarations.h"

//	scalar and array expansion
//	wrap-around scalar under an if

TYPE s258(int count) {
	int s = 0.;
	for (int i = 0; i < count*8; ++i) {
		if (a[i] > 0.) {
			s = d[i] * d[i];
		}
		b[i] = s * c[i] + d[i];
		e[i] = (s + (float)1.) * aa[0][i];
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s258(count);
}