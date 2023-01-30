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

//	scalar and array expansion
//	scalar expansion

TYPE s3251(int count) {
  for (int i = 0; i < count*8-1; i++) {
		a[i+1] = b[i]+c[i];
		b[i]   = c[i]*e[i];
		d[i]   = a[i]*e[i];
  }
  return 0;
}

int main() {
  return 0;
}