#include "declarations.h"


TYPE s452(int count) {
  for (int i = 0; i < count*8; i++) {
	  a[i] = b[i] + c[i] * (i+1);
  }
  return 0;
}


int nondet();

int main() {
  int count = nondet();
  s452(count);
}