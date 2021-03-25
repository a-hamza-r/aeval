#include "declarations.h"

//	scalar and array expansion
//	array expansion

TYPE s257(int count) {
	for (int i = 1; i < count; i++) {
		for (int j = 0; j < count; j++) {
			a[i] = aa[j][i] - a[i-1];
			aa[j][i] = a[i] + bb[j][i];
		}
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s257(count);
}