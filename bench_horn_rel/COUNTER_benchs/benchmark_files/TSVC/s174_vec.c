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

//	symbolics
//	expression in loop bounds and subscripts

TYPE s174(int count) {
  int k = count*4;
  for (int i = 0; i < k; i+=4) {
    a[i+k] = a[i] + b[i];
    a[i+1+k] = a[i+1] + b[i+1];
    a[i+2+k] = a[i+2] + b[i+2];
    a[i+3+k] = a[i+3] + b[i+3];
  }
  return 0;
}

int main() {
	return 0;
}