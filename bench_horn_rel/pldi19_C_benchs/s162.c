#include "declarations.h"


TYPE s162(int count) {
  for (int i = 0; i < count*8-1; i++) {
    a[i] = a[i + 1] + b[i] * c[i];
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s162(count);
}