#include "declarations.h"

//	crossing thresholds
//	index set splitting
//	reverse data access

TYPE s281(int count) {
	for (int i = 0; i < count*8; i++) {
		x = a[count*8-i-1] + b[i] * c[i];
		a[i] = x-(float)1.0;
		b[i] = x;
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s281(count);
}