#include "declarations.h"


TYPE s1351(int count) {
  TYPE* __restrict__ A = a;
  TYPE* __restrict__ B = b;
  TYPE* __restrict__ C = c;
  for (int i = 0; i < count*8; i++) {
    *A = *B + *C;
    A++;
    B++;
    C++;
  }
  return 0;
}


int nondet();

int main() {
  int count = nondet();
  s1351(count);
}