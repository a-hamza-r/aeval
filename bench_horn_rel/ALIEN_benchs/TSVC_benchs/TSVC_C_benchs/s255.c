#include "declarations.h"

//	scalar and array expansion
//	carry around variables, 2 levels

TYPE s255(int count) {
	x = b[count*8-1];
	y = b[count*8-2];
	for (int i = 0; i < count*8; i++) {
		a[i] = (b[i] + x + y) * (float).333;
		y = x;
		x = b[i];
	}
  return 0;
}

/*after carry around variables:

TYPE s255(int count) {
	a[0] = (b[0] + b[count*8-1] + b[count*8-2]) * (float).333;
	a[1] = (b[1] + b[0] + b[count*8-1]) * (float).333;
	for (int i = 2; i < count*8; i++) {
		a[i] = (b[i] + b[i-1] + b[i-2]) * (float).333;
	}
  return 0;
}*/


int nondet();

int main() {
	int count = nondet();
	s255(count);
}