#include "declarations.h"


TYPE s311(int count) {
  TYPE sum = 0;
  for (int i = 0; i < count*8; i++) {
    sum += a[i];
  }
  return sum;
}


int nondet();

int main() {
	int count = nondet();
	s311(count);
}