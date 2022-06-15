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

//	control flow
//	deriving assertions

TYPE s162(int count, int k) {
  if (k > 0) {
    a[0] = a[0 + k] + b[0] * c[0];
    a[1] = a[1 + k] + b[1] * c[1];
    a[2] = a[2 + k] + b[2] * c[2];
    a[3] = a[3 + k] + b[3] * c[3];
    a[4] = a[4 + k] + b[4] * c[4];
    a[5] = a[5 + k] + b[5] * c[5];
    a[6] = a[6 + k] + b[6] * c[6];
    for (int i = 7; i < count*8-1; i+=8) {
      a[i] = a[i + k] + b[i] * c[i];
      a[i+1] = a[i+1 + k] + b[i+1] * c[i+1];
      a[i+2] = a[i+2 + k] + b[i+2] * c[i+2];
      a[i+3] = a[i+3 + k] + b[i+3] * c[i+3];
      a[i+4] = a[i+4 + k] + b[i+4] * c[i+4];
      a[i+5] = a[i+5 + k] + b[i+5] * c[i+5];
      a[i+6] = a[i+6 + k] + b[i+6] * c[i+6];
      a[i+7] = a[i+7 + k] + b[i+7] * c[i+7];
    }
  }
  return 0;
}

int main() {
	return 0;
}