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
  if (count) {
    array[0+64] = array[0] + a[0];
    array[0+1+64] = array[0+1] + a[0+1];
    array[0+2+64] = array[0+2] + a[0+2];
    array[0+3+64] = array[0+3] + a[0+3];
    array[0+4+64] = array[0+4] + a[0+4];
    array[0+5+64] = array[0+5] + a[0+5];
    array[0+6+64] = array[0+6] + a[0+6];
  }
  for (int i = 7; i < count*8 - 1; i+=8) {
    array[i+64] = array[i] + a[i];
    array[i+1+64] = array[i+1] + a[i+1];
    array[i+2+64] = array[i+2] + a[i+2];
    array[i+3+64] = array[i+3] + a[i+3];
    array[i+4+64] = array[i+4] + a[i+4];
    array[i+5+64] = array[i+5] + a[i+5];
    array[i+6+64] = array[i+6] + a[i+6];
    array[i+7+64] = array[i+7] + a[i+7];
  }
  return 0;
}

int main() {
	return 0;
}