#include "declarations.h"

//    non-local goto's
//    stop statement

TYPE s481(int count) {
  for (int i = 0; i < count*8; i++) {
    if (d[i] < 0) {
        exit (0);
    }
    a[i] += b[i] * c[i];
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s481(count);
}