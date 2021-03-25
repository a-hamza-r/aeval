#include "declarations.h"

//	symbolics
//	symbolic dependence tests

TYPE s171(int count, int inc) {
	for (int i = 0; i < count*8; i++) {
		a[i * inc] += b[i];
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	int inc = nondet();
	s171(count, inc);
}