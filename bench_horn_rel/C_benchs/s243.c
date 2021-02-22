#include "declarations.h"


TYPE s243(int count) {
  for (int i = 0; i < count*8-1; i++) {
    a[i] = b[i] + c[i  ] * d[i];
    b[i] = a[i] + d[i  ] * e[i];
    a[i] = b[i] + a[i+1] * d[i];
  }
  return 0;
}


int nondet();

int main() {
  int count = nondet();
  s243(count);
}