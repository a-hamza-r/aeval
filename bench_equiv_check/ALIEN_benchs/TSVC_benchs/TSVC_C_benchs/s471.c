#include "declarations.h"

//  call statement

TYPE s471(int count) {
  for (int i = 0; i < count*8; i++) {
    x[i] = b[i] + d[i] * d[i];
    b[i] = c[i] + d[i] * e[i];
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s471(count);
}