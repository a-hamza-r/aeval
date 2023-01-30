#include "declarations.h"

//    recurrences
//    coupled recurrence

TYPE s323(int count) {
  for (int i = 1; i < count*8; i++) {
    a[i] = b[i-1] + c[i] * d[i];
    b[i] = a[i] + c[i] * e[i];
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s323(count);
}