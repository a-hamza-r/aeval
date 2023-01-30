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

//	linear dependence testing
//	loop reversal

TYPE s112(int count) {
  for (int i = count*8-1; i >= 8; i-=8) {
    a[i] = a[i-1] + b[i];
    a[i-1] = a[i-2] + b[i-1];
    a[i-2] = a[i-3] + b[i-2];
    a[i-3] = a[i-4] + b[i-3];
    a[i-4] = a[i-5] + b[i-4];
    a[i-5] = a[i-6] + b[i-5];
    a[i-6] = a[i-7] + b[i-6];
    a[i-7] = a[i-8] + b[i-7];
  }
  a[7] = a[6] + b[7];
  a[6] = a[5] + b[6];
  a[5] = a[4] + b[5];
  a[4] = a[3] + b[4];
  a[3] = a[2] + b[3];
  a[2] = a[1] + b[2];
  a[1] = a[0] + b[1];
  return 0;
}


int main() {
	return 0;
}