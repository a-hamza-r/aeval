#include "declarations.h"

//	scalar and array expansion
//	array expansion

TYPE s257(int count) {
	for (int i = 1; i < count*8; i++) {
		for (int j = 0; j < count*8; j++) {
			a[i] = aa[j][i] - a[i-1];
			aa[j][i] = a[i] + bb[j][i];
		}
	}
  return 0;
}

/*
// after interchanging loops
TYPE s257(int count) {
	for (int j = 0; j < count*8; j++) {
		for (int i = 1; i < count*8; i++) {
			a[i] = aa[j][i] - a[i-1];
			aa[j][i] = a[i] + bb[j][i];
		}
	}
  return 0;
}
*/


int nondet();

int main() {
	int count = nondet();
	s257(count);
}