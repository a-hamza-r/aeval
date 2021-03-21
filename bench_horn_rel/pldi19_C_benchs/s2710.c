#include "declarations.h"


// doesn't vectorize
TYPE s2710(int count, int x) {
  for (int i = 0; i < count*8; i++) {
    if (a[i] > b[i]) {
      a[i] += b[i] * d[i];
      if (count*8 > 10) {
        c[i] += d[i] * d[i];
      } else {
        c[i] = d[i] * e[i] + 1;
      }
    } else {
      b[i] = a[i] + e[i] * e[i];
      if (x > 0) {
        c[i] = a[i] + d[i] * d[i];
      } else {
        c[i] += e[i] * e[i];
      }
    }
  }
  return 0;
}


int nondet();

int main() {
  int count = nondet();
  int x = nondet();
  s2710(count, x);
}