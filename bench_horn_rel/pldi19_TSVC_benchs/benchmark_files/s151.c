#include "declarations.h"

//	global data flow analysis
//	forward substitution

TYPE s151(int count) {
	int m = 1;
	for (int i = 0; i < count*8 - 1; i++) {
		a[i] = a[i + m] + b[i];
	}
	return 0;
}

/*after forward substitution:

TYPE s151(int count) {
	for (int i = 0; i < count*8 - 1; i++) {
		a[i] = a[i + 1] + b[i];
	}
	return 0;
}*/


int nondet();

int main() {
	int count = nondet();
	s151(count);
}