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

TYPE s173(int count) {
  int k = count*4;
  for (int i = 0; i < k; i++) {
    a[i+k] = a[i] + b[i];
  }
  return 0;
}

int main() {
	return 0;
}