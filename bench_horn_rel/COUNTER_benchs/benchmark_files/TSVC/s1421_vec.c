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

TYPE s1421(int count) {
  for (int i = 0; i < count*4; i+=4) {
    b[i] = b[count*4+i] + a[i];
    b[i+1] = b[count*4+i+1] + a[i+1];
    b[i+2] = b[count*4+i+2] + a[i+2];
    b[i+3] = b[count*4+i+3] + a[i+3];
  }
  return 0;
}

int main() {
	return 0;
}