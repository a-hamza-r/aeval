#include "declarations.h"


TYPE s212(int count) {
	for (int i = 0; i < count*8-1; i++) {
		a[i] *= c[i];
		b[i] += a[i + 1] * d[i];
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s212(count);
}