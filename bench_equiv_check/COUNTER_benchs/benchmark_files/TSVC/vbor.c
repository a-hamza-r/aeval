#include "declarations.h"

#include <stdlib.h>
#include <math.h>
#include <stdio.h>
#include <sys/param.h>
#include <sys/times.h>
#include <sys/types.h>
#include <time.h>
#include <malloc.h>
#include <string.h>
#include <assert.h>
#include "eqchecker_helper.h"

//    control loops
//    basic operations rates, isolate arithmetic from memory traffic
//    all combinations of three, 59 flops for 6 loads and 1 store.

TYPE vbor(int count) {
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

int main() {
  return 0;
}