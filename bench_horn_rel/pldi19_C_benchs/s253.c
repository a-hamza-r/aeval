#include "declarations.h"


TYPE s253(int count) {
	for (int i = 0; i < count*8; i++) {
		if (a[i] > b[i]) {
			s = a[i] - b[i] * d[i];
			c[i] += s;
			a[i] = s;
		}
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s253(count);
}