#include "declarations.h"


TYPE s251(int count) {
  TYPE s;
  for (int i = 0; i < count*8; i++) {
   	s = b[i] + c[i] * d[i];
	a[i] = s * s;
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s251(count);
}