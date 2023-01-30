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

//  call statement

TYPE s471(int count) {
  for (int i = 0; i < count*8; i+=8) {
    x[i] = b[i] + d[i] * d[i];
    b[i] = c[i] + d[i] * e[i];

    x[i+1] = b[i+1] + d[i+1] * d[i+1];
    b[i+1] = c[i+1] + d[i+1] * e[i+1];

    x[i+2] = b[i+2] + d[i+2] * d[i+2];
    b[i+2] = c[i+2] + d[i+2] * e[i+2];

    x[i+3] = b[i+3] + d[i+3] * d[i+3];
    b[i+3] = c[i+3] + d[i+3] * e[i+3];

    x[i+4] = b[i+4] + d[i+4] * d[i+4];
    b[i+4] = c[i+4] + d[i+4] * e[i+4];

    x[i+5] = b[i+5] + d[i+5] * d[i+5];
    b[i+5] = c[i+5] + d[i+5] * e[i+5];

    x[i+6] = b[i+6] + d[i+6] * d[i+6];
    b[i+6] = c[i+6] + d[i+6] * e[i+6];

    x[i+7] = b[i+7] + d[i+7] * d[i+7];
    b[i+7] = c[i+7] + d[i+7] * e[i+7];
  }
  return 0;
}

int main() {
  return 0;
}