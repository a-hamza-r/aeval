#include "declarations.h"

//	control loops
//	vector dot product reduction

TYPE vdotr(int count) {
  TYPE sum = 0;
  for (int i = 0; i < count*8; i++) {
    sum += a[i]*b[i];
  }
  return sum;
}


int nondet();

int main() {
  int count = nondet();
  vdotr(count);
}