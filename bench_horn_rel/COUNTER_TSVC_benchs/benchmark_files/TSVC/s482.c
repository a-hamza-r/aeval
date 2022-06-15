#include "declarations.h"

//    non-local goto's
//    other loop exit with code before exit

TYPE s482(int count) {
  for (int i = 0; i < count*8; i++) {
    a[i] += b[i] * c[i];
    if (c[i] > b[i]) break;
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s482(count);
}