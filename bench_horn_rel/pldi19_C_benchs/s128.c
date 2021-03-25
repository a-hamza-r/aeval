#include "declarations.h"

//	induction variables
//	coupled induction variables
//	jump in data access

TYPE s128(int count) {
	int j = -1, k;
	for (int i = 0; i < count*4; i++) {
		k = j + 1;
		a[i] = b[k] - d[i];
		j = k + 1;
		b[k] = a[i] + c[k];
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s128(count);
}