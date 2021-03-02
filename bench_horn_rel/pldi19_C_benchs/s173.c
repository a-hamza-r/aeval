#include "declarations.h"


TYPE s173(int count) {
  int k = count*4;
  for (int i = 0; i < k; i++) {
    a[i+k] = a[i] + b[i];
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s173(count);
}