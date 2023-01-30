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
//	no dependence - vectorizable

TYPE s421(int count) {
  for (int i = 0; i < count*8; i+=8) {
    xx[i] = xx[i+1] + a[i];
    xx[i+1] = xx[i+1+1] + a[i+1];
    xx[i+2] = xx[i+2+1] + a[i+2];
    xx[i+3] = xx[i+3+1] + a[i+3];
    xx[i+4] = xx[i+4+1] + a[i+4];
    xx[i+5] = xx[i+5+1] + a[i+5];
    xx[i+6] = xx[i+6+1] + a[i+6];
    xx[i+7] = xx[i+7+1] + a[i+7];
  }
  return 0;
}

int main() {
	return 0;
}