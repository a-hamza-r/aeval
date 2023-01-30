#include "declarations.h"

//    reductions
//    sum reduction saving running sums

TYPE s3112(int count) {
  TYPE sum = 0;
  for (int i = 0; i < count*8; i++) {
    sum += a[i];
    b[i] = sum;
  }
  return sum;
}


int nondet();

int main() {
	int count = nondet();
	s3112(count);
}