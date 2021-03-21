#include "declarations.h"


TYPE s1113(int count) {
	for (int i = 0; i < count*8; i++) {
		a[i] = a[count*4] + b[i];
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s1113(count);
}