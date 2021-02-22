#include "declarations.h"


TYPE s111(int count) {
  for (int i = 1; i < count*8; i+=2) {
    a[i] = a[i-1] + b[i];
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s111(count);
}