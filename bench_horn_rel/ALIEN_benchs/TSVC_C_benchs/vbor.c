#include "declarations.h"

//    control loops
//    basic operations rates, isolate arithmetic from memory traffic
//    all combinations of three, 59 flops for 6 loads and 1 store.

int vbor(int count) {
  for (int i = 0; i < count*8; i++) {
    a1 = a[i];
    b1 = b[i];
    c1 = c[i];
    d1 = d[i];
    e1 = e[i];
    f1 = aa[0][i];
    a1 = a1 * b1 * c1 + a1 * b1 * d1 + a1 * b1 * e1 + a1 * b1 * f1 +
        a1 * c1 * d1 + a1 * c1 * e1 + a1 * c1 * f1 + a1 * d1 * e1
        + a1 * d1 * f1 + a1 * e1 * f1;
    b1 = b1 * c1 * d1 + b1 * c1 * e1 + b1 * c1 * f1 + b1 * d1 * e1 +
        b1 * d1 * f1 + b1 * e1 * f1;
    c1 = c1 * d1 * e1 + c1 * d1 * f1 + c1 * e1 * f1;
    d1 = d1 * e1 * f1;
    x[i] = a1 * b1 * c1 * d1;
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	vbor(count);
}