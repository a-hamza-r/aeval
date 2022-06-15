#include "declarations.h"

//	linear dependence testing
//	no dependence - vectorizable

TYPE s1421(int count) {
  for (int i = 0; i < count*4; i++) {
    b[i] = b[count*4+i] + a[i];
  }
  return 0;
}

int nondet();

int main() {
	int count = nondet();
	s1421(count);
}