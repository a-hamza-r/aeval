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
//	loop reversal

TYPE s112(int count) {
  for (int i = count*8-1; i >= 1; i--) {
    a[i] = a[i-1] + b[i];
  }
  return 0;
}

int main() {
	return 0;
}