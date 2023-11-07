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

TYPE s111(int count) {
  for (int i = 1; i < count*8; i+=8) {
    a[i] = a[i-1] + b[i];
    a[(i+2)] = a[(i+2)-1] + b[(i+2)];
    a[(i+4)] = a[(i+4)-1] + b[(i+4)];
    a[(i+6)] = a[(i+6)-1] + b[(i+6)];
  }
  return 0;
}


int main() {
	return 0;
}