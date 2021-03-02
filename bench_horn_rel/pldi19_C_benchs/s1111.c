#include "declarations.h"


TYPE s1111(int count) {
  for (int i = 0; i < count*4; i++) {
	  a[2*i] = c[i] * b[i] + d[i] * b[i] + c[i] * c[i] + d[i] * b[i] + d[i] * c[i];
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s1111(count);
}