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

TYPE s422(int count) {
  for (int i = 0; i < count*8; i+=8) {
    array[i+4] = array[i + 8] + a[i];
    array[i+1+4] = array[i+1 + 8] + a[i+1];
    array[i+2+4] = array[i+2 + 8] + a[i+2];
    array[i+3+4] = array[i+3 + 8] + a[i+3];
    array[i+4+4] = array[i+4 + 8] + a[i+4];
    array[i+5+4] = array[i+5 + 8] + a[i+5];
    array[i+6+4] = array[i+6 + 8] + a[i+6];
    array[i+7+4] = array[i+7 + 8] + a[i+7];
  }
  return 0;
}

int main() {
	return 0;
}