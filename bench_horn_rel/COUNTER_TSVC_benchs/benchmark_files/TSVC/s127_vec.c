#include "declarations.h"

//  induction variable recognition
//  induction variable with multiple increments
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

TYPE s127(int count) {
  a[2*0] = b[0] + c[0] * d[0];
  a[2*0+1] = b[0] + d[0] * e[0];

  a[2*1] = b[1] + c[1] * d[1];
  a[2*1+1] = b[1] + d[1] * e[1];

  a[2*2] = b[2] + c[2] * d[2];
  a[2*2+1] = b[2] + d[2] * e[2];

  for (int i = 3; i < count*4-1; i+=4) {
    a[2*i] = b[i] + c[i] * d[i];
    a[2*i+1] = b[i] + d[i] * e[i];

    a[2*(i+1)] = b[(i+1)] + c[(i+1)] * d[(i+1)];
    a[2*(i+1)+1] = b[(i+1)] + d[(i+1)] * e[(i+1)];

    a[2*(i+2)] = b[(i+2)] + c[(i+2)] * d[(i+2)];
    a[2*(i+2)+1] = b[(i+2)] + d[(i+2)] * e[(i+2)];

    a[2*(i+3)] = b[(i+3)] + c[(i+3)] * d[(i+3)];
    a[2*(i+3)+1] = b[(i+3)] + d[(i+3)] * e[(i+3)];
  }
  return 0;
}

int main() {
  return 0;
}