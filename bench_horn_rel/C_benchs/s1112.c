#include "declarations.h"


TYPE s1112(int count) {
  for (int i = count*8-1; i >= 0; i--) {
    a[i] = b[i] + 1;
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s1112(count);
}