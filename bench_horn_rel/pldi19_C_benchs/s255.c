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


int nondet();

int main() {
	int count = nondet();
	s255(count);
}