#include "declarations.h"


TYPE s175(int count, int inc) {
	for (int i = 0; i < count*8-1; i += inc) {
		a[i] = a[i + inc] + b[i];
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	int inc = nondet();
	s175(count, inc);
}