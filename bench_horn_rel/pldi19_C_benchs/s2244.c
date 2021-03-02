#include "declarations.h"


TYPE s2244(int count) {
	for (int i = 0; i < count*8-1; i++) {
		a[i+1] = b[i] + e[i];
		a[i] = b[i] + c[i];
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s2244(count);
}