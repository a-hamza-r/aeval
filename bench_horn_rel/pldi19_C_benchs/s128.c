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


/*after induction variables recognition:

TYPE s128(int count) {
	for (int i = 0; i < count*4; i++) {
		a[i] = b[2*i] - d[i];
		b[2*i] = a[i] + c[2*i];
	}
  return 0;
}*/

int nondet();

int main() {
	int count = nondet();
	s128(count);
}