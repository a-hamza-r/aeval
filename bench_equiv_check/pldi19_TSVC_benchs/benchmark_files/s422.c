#include "declarations.h"

//	linear dependence testing
//	no dependence - vectorizable

TYPE s422(int count) {
  for (int i = 0; i < count*8; i++) {
    array[i+4] = array[i + 8] + a[i];
  }
  return 0;
}

int nondet();

int main() {
	int count = nondet();
	s422(count);
}