#include "declarations.h"

//	loop distribution is needed to be able to interchange

TYPE s2275(int count) {
	for (int i = 0; i < count; i++) {
		for (int j = 0; j < count; j++) {
			aa[j][i] = aa[j][i] + bb[j][i] * cc[j][i];
		}
		a[i] = b[i] + c[i] * d[i];
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s2275(count);
}