#include "declarations.h"


TYPE sum1d(int count) {
  TYPE sum = 0;
  for (int i = 0; i < count*8; i++) {
      a[i] = c[i] + d[i];
      sum += a[i];
      b[i] = c[i] + e[i];
      sum += b[i];
  }
  return sum;
}


int nondet();

int main() {
	int count = nondet();
	sum1d(count);
}