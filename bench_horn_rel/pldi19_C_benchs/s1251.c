#include "declarations.h"


TYPE s1251(int count) {
  TYPE s;
  for (int i = 0; i < count*8; i++) {
    s = b[i]+c[i];
    b[i] = a[i]+d[i];
    a[i] = s*e[i];
  }
  return 0;
}


int nondet();

int main() {
  int count = nondet();
  s1251(count);
}