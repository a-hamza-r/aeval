#include "declarations.h"


TYPE s291(int count) {
	int im1 = count*8-1;
	for (int i = 0; i < count*8; i++) {
		a[i] = (b[i] + b[im1]) * (float).5;
		im1 = i;
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s291(count);
}