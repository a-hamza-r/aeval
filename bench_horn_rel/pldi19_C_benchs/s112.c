#include "declarations.h"


TYPE s112(int count) {
  for (int i = count*8-1; i >= 1; i--) {
    a[i] = a[i-1] + b[i];
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s112(count);
}