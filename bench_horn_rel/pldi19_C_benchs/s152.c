#include "declarations.h"


TYPE s152(int count) {
	for (int i = 0; i < count*8; i++) {
		b[i] = d[i] * e[i];
		a[i] += b[i] * c[i];
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s152(count);
}