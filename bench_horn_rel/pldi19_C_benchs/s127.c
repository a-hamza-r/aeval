#include "declarations.h"


TYPE s127(int count) {
  int j = -1;
  for (int i = 0; i < count*4-1; i++) {
    j++;
    a[j] = b[i] + c[i] * d[i];
    j++;
    a[j] = b[i] + d[i] * e[i];
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s127(count);
}