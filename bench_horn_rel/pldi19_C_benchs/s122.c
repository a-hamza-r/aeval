#include "declarations.h"

//	induction variable recognition
//	variable lower and upper bound, and stride
//	reverse data access and jump in data access

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