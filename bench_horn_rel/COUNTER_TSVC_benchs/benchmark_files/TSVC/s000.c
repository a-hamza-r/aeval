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
  for (int i = 0; i < count*8; i++) {
    a[i] = b[i] + 1;
  }
  return 0;
}

int main() {
	return 0;
}