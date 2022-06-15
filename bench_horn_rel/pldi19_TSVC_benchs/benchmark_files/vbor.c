#include "declarations.h"

//    control loops
//    basic operations rates, isolate arithmetic from memory traffic
//    all combinations of three, 59 flops for 6 loads and 1 store.

TYPE 
__attribute__((noinline))
vbor(TYPE* a, TYPE* b, TYPE *c, TYPE *d, TYPE *e, TYPE **aa, TYPE *x, int count) {
  for (int i = 0; i < count*8; i++) {
    TYPE a1 = a[i];
    TYPE b1 = b[i];
    TYPE c1 = c[i];
    TYPE d1 = d[i];
    TYPE e1 = e[i];
    TYPE f1 = aa[0][i];
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

TYPE 
__attribute__((noinline))
vbor_vec(TYPE* a, TYPE* b, TYPE *c, TYPE *d, TYPE *e, TYPE **aa, TYPE *x, int count) {
  for (int i = 0; i < count*8; i+=8) {
    TYPE a1 = a[i];
    TYPE b1 = b[i];
    TYPE c1 = c[i];
    TYPE d1 = d[i];
    TYPE e1 = e[i];
    TYPE f1 = aa[0][i];
    a1 = a1 * b1 * c1 + a1 * b1 * d1 + a1 * b1 * e1 + a1 * b1 * f1 +
        a1 * c1 * d1 + a1 * c1 * e1 + a1 * c1 * f1 + a1 * d1 * e1
        + a1 * d1 * f1 + a1 * e1 * f1;
    b1 = b1 * c1 * d1 + b1 * c1 * e1 + b1 * c1 * f1 + b1 * d1 * e1 +
        b1 * d1 * f1 + b1 * e1 * f1;
    c1 = c1 * d1 * e1 + c1 * d1 * f1 + c1 * e1 * f1;
    d1 = d1 * e1 * f1;
    x[i] = a1 * b1 * c1 * d1;

    a1 = a[i+1];
    b1 = b[i+1];
    c1 = c[i+1];
    d1 = d[i+1];
    e1 = e[i+1];
    f1 = aa[0][i+1];
    a1 = a1 * b1 * c1 + a1 * b1 * d1 + a1 * b1 * e1 + a1 * b1 * f1 +
        a1 * c1 * d1 + a1 * c1 * e1 + a1 * c1 * f1 + a1 * d1 * e1
        + a1 * d1 * f1 + a1 * e1 * f1;
    b1 = b1 * c1 * d1 + b1 * c1 * e1 + b1 * c1 * f1 + b1 * d1 * e1 +
        b1 * d1 * f1 + b1 * e1 * f1;
    c1 = c1 * d1 * e1 + c1 * d1 * f1 + c1 * e1 * f1;
    d1 = d1 * e1 * f1;
    x[i+1] = a1 * b1 * c1 * d1;

    a1 = a[i+2];
    b1 = b[i+2];
    c1 = c[i+2];
    d1 = d[i+2];
    e1 = e[i+2];
    f1 = aa[0][i+2];
    a1 = a1 * b1 * c1 + a1 * b1 * d1 + a1 * b1 * e1 + a1 * b1 * f1 +
        a1 * c1 * d1 + a1 * c1 * e1 + a1 * c1 * f1 + a1 * d1 * e1
        + a1 * d1 * f1 + a1 * e1 * f1;
    b1 = b1 * c1 * d1 + b1 * c1 * e1 + b1 * c1 * f1 + b1 * d1 * e1 +
        b1 * d1 * f1 + b1 * e1 * f1;
    c1 = c1 * d1 * e1 + c1 * d1 * f1 + c1 * e1 * f1;
    d1 = d1 * e1 * f1;
    x[i+2] = a1 * b1 * c1 * d1;

    a1 = a[i+3];
    b1 = b[i+3];
    c1 = c[i+3];
    d1 = d[i+3];
    e1 = e[i+3];
    f1 = aa[0][i+3];
    a1 = a1 * b1 * c1 + a1 * b1 * d1 + a1 * b1 * e1 + a1 * b1 * f1 +
        a1 * c1 * d1 + a1 * c1 * e1 + a1 * c1 * f1 + a1 * d1 * e1
        + a1 * d1 * f1 + a1 * e1 * f1;
    b1 = b1 * c1 * d1 + b1 * c1 * e1 + b1 * c1 * f1 + b1 * d1 * e1 +
        b1 * d1 * f1 + b1 * e1 * f1;
    c1 = c1 * d1 * e1 + c1 * d1 * f1 + c1 * e1 * f1;
    d1 = d1 * e1 * f1;
    x[i+3] = a1 * b1 * c1 * d1;

    a1 = a[i+4];
    b1 = b[i+4];
    c1 = c[i+4];
    d1 = d[i+4];
    e1 = e[i+4];
    f1 = aa[0][i+4];
    a1 = a1 * b1 * c1 + a1 * b1 * d1 + a1 * b1 * e1 + a1 * b1 * f1 +
        a1 * c1 * d1 + a1 * c1 * e1 + a1 * c1 * f1 + a1 * d1 * e1
        + a1 * d1 * f1 + a1 * e1 * f1;
    b1 = b1 * c1 * d1 + b1 * c1 * e1 + b1 * c1 * f1 + b1 * d1 * e1 +
        b1 * d1 * f1 + b1 * e1 * f1;
    c1 = c1 * d1 * e1 + c1 * d1 * f1 + c1 * e1 * f1;
    d1 = d1 * e1 * f1;
    x[i+4] = a1 * b1 * c1 * d1;

    a1 = a[i+5];
    b1 = b[i+5];
    c1 = c[i+5];
    d1 = d[i+5];
    e1 = e[i+5];
    f1 = aa[0][i+5];
    a1 = a1 * b1 * c1 + a1 * b1 * d1 + a1 * b1 * e1 + a1 * b1 * f1 +
        a1 * c1 * d1 + a1 * c1 * e1 + a1 * c1 * f1 + a1 * d1 * e1
        + a1 * d1 * f1 + a1 * e1 * f1;
    b1 = b1 * c1 * d1 + b1 * c1 * e1 + b1 * c1 * f1 + b1 * d1 * e1 +
        b1 * d1 * f1 + b1 * e1 * f1;
    c1 = c1 * d1 * e1 + c1 * d1 * f1 + c1 * e1 * f1;
    d1 = d1 * e1 * f1;
    x[i+5] = a1 * b1 * c1 * d1;

    a1 = a[i+6];
    b1 = b[i+6];
    c1 = c[i+6];
    d1 = d[i+6];
    e1 = e[i+6];
    f1 = aa[0][i+6];
    a1 = a1 * b1 * c1 + a1 * b1 * d1 + a1 * b1 * e1 + a1 * b1 * f1 +
        a1 * c1 * d1 + a1 * c1 * e1 + a1 * c1 * f1 + a1 * d1 * e1
        + a1 * d1 * f1 + a1 * e1 * f1;
    b1 = b1 * c1 * d1 + b1 * c1 * e1 + b1 * c1 * f1 + b1 * d1 * e1 +
        b1 * d1 * f1 + b1 * e1 * f1;
    c1 = c1 * d1 * e1 + c1 * d1 * f1 + c1 * e1 * f1;
    d1 = d1 * e1 * f1;
    x[i+6] = a1 * b1 * c1 * d1;

    a1 = a[i+7];
    b1 = b[i+7];
    c1 = c[i+7];
    d1 = d[i+7];
    e1 = e[i+7];
    f1 = aa[0][i+7];
    a1 = a1 * b1 * c1 + a1 * b1 * d1 + a1 * b1 * e1 + a1 * b1 * f1 +
        a1 * c1 * d1 + a1 * c1 * e1 + a1 * c1 * f1 + a1 * d1 * e1
        + a1 * d1 * f1 + a1 * e1 * f1;
    b1 = b1 * c1 * d1 + b1 * c1 * e1 + b1 * c1 * f1 + b1 * d1 * e1 +
        b1 * d1 * f1 + b1 * e1 * f1;
    c1 = c1 * d1 * e1 + c1 * d1 * f1 + c1 * e1 * f1;
    d1 = d1 * e1 * f1;
    x[i+7] = a1 * b1 * c1 * d1;
  }
  return 0;
}

int main() {
	return 0;
}