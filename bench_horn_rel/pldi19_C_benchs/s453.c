#include "declarations.h"


TYPE s453(int count) {
  TYPE s = 0;
  for (int i = 0; i < count*8; i++) {
    s += (TYPE)2;
    a[i] = s * b[i];
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s453(count);
}