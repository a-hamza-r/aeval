#include "declarations.h"

//	linear dependence testing
//	no dependence - vectorizable

TYPE s421(int count) {
  for (int i = 0; i < count*8; i++) {
    xx[i] = xx[i+1] + a[i];
  }
  return 0;
}

int nondet();

int main() {
	int count = nondet();
	s421(count);
}