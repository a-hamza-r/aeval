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

TYPE s424(int count) {
  for (int i = 0; i < count*8 - 1; i++) {
    array[i+64] = array[i] + a[i];
  }
  return 0;
}

int main() {
	return 0;
}