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

//  symbolics
//  convolution

/** vectorizes with gcc */
TYPE s176(int count) {
  int m = count*4;
  for (int j = 0; j < m; j++) {
    for (int i = 0; i < m; i+=4) {
      a[i] += b[i+m-j-1] * c[j];
      a[i+1] += b[i+1+m-j-1] * c[j];
      a[i+2] += b[i+2+m-j-1] * c[j];
      a[i+3] += b[i+3+m-j-1] * c[j];
    }
  }
  return 0;
}

int main() {
  return 0;
}