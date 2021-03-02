#include "declarations.h"


TYPE s000(int count) {
  for (int i = 0; i < count*8; i++) {
    a[i] = b[i] + 1;
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s000(count);
}