#include "declarations.h"

//	node splitting
//	preloading necessary to allow vectorization

TYPE s241(int count) {
	for (int i = 0; i < count*8-1; i++) {
		a[i] = b[i] * c[i  ] * d[i];
		b[i] = a[i] * a[i+1] * d[i];
	}
	return 0;
}


/*after node splitting:

TYPE s241(int count) {
	TYPE e[count*8-1];
	for (int i = 0; i < count*8-1; i++) {
		e[i] = a[i+1];
		a[i] = b[i] * c[i  ] * d[i];
		b[i] = a[i] * e[i] * d[i];
	}
	return 0;
}*/

int nondet();

int main() {
	int count = nondet();
	s241(count);
}