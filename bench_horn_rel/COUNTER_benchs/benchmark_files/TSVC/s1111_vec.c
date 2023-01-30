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

//	no dependence - vectorizable
//	jump in data access

TYPE s1111(int count) {
  for (int i = 0; i < count*4; i+=4) {
	  a[2*i] = c[i] * b[i] + d[i] * b[i] + c[i] * c[i] + d[i] * b[i] + d[i] * c[i];
    a[2*(i+1)] = c[(i+1)] * b[(i+1)] + d[(i+1)] * b[(i+1)] + c[(i+1)] * c[(i+1)] + d[(i+1)] * b[(i+1)] + d[(i+1)] * c[(i+1)];
    a[2*(i+2)] = c[(i+2)] * b[(i+2)] + d[(i+2)] * b[(i+2)] + c[(i+2)] * c[(i+2)] + d[(i+2)] * b[(i+2)] + d[(i+2)] * c[(i+2)];
    a[2*(i+3)] = c[(i+3)] * b[(i+3)] + d[(i+3)] * b[(i+3)] + c[(i+3)] * c[(i+3)] + d[(i+3)] * b[(i+3)] + d[(i+3)] * c[(i+3)];
  }
  return 0;
}


int main() {
	return 0;
}