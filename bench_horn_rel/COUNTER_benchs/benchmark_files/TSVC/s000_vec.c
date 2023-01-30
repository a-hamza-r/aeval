#include "declarations.h"

//	linear dependence testing
//	no dependence - vectorizable

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

TYPE s000(int count) {
  for (int i = 0; i < count*8; i+=8) {
    a[i] = b[i] + 1;
    a[i+1] = b[i+1] + 1;
    a[i+2] = b[i+2] + 1;
    a[i+3] = b[i+3] + 1;
    a[i+4] = b[i+4] + 1;
    a[i+5] = b[i+5] + 1;
    a[i+6] = b[i+6] + 1;
    a[i+7] = b[i+7] + 1;
  }
  return 0;
}

int main() {
	return 0;
}