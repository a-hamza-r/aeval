#include "declarations.h"

//	scalar and array expansion
//	carry around variable

TYPE s254(int count) {
	int x = b[count*8-1];
	for (int i = 0; i < count*8; i++) {
		a[i] = (b[i] + x) * (float).5;
		x = b[i];
	}
	return 0;
}


/*after carry around variable: 

TYPE s254(int count) {
	a[0] = (b[0] + b[count*8-1]) * (float).5;
	for (int i = 1; i < count*8; i++) {
		a[i] = (b[i] + b[i-1]) * (float).5;
	}
	return 0;
}*/

int nondet();

int main() {
	int count = nondet();
	s254(count);
}