#include "declarations.h"

//    reductions
//    conditional sum reduction

TYPE s3111(int count) {
  TYPE sum = 0;
  for (int i = 0; i < count*8; i++) {
      if (a[i] > 0) {
          sum += a[i];
      }
  }
  return sum;
}


int nondet();

int main() {
	int count = nondet();
	s3111(count);
}