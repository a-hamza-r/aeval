#include "declarations.h"

//	loop distribution is needed to be able to interchange

TYPE s2275(int count) {
	for (int i = 0; i < count*8; i++) {
		for (int j = 0; j < count*8; j++) {
			aa[j][i] = aa[j][i] + bb[j][i] * cc[j][i];
		}
		a[i] = b[i] + c[i] * d[i];
	}
  return 0;
}

/*
// after interchanging loops
TYPE s2275(int count) {
	for (int j = 0; j < count*8; j++) {
		for (int i = 0; i < count*8; i++) {
			aa[j][i] = aa[j][i] + bb[j][i] * cc[j][i];
		}
		a[j] = b[j] + c[j] * d[j];
	}
  return 0;
}
*/

int nondet();

int main() {
	int count = nondet();
	s2275(count);
}