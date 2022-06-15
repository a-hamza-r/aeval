#include "declarations.h"

//    intrinsic functions
//    intrinsics

TYPE s451(int count) {
  for (int i = 0; i < count*8; i++) {
    a[i] = sinf(b[i]) + cosf(c[i]);
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s451(count);
}