#include "declarations.h"

//	loop peeling
//	wrap around variable, 2 levels
//	similar to S291

TYPE s292(int count) {
	int im1 = count*8-1;
	int im2 = count*8-2;
	for (int i = 0; i < count*8; i++) {
		a[i] = (b[i] + b[im1] + b[im2]) * (float).333;
		im2 = im1;
		im1 = i;
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s292(count);
}