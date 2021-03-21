#include "declarations.h"


TYPE s221(int count) {
	for (int i = 1; i < count*8; i++) {
		a[i] += c[i] * d[i];
		b[i] = b[i - 1] + a[i] + d[i];
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s221(count);
}