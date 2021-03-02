#include "declarations.h"


TYPE s122(int count) {
  int k = 0;
  for (int i = 1; i < count*8; i++) {
    k++;
    a[i] += b[count*8-k];
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s122(count);
}