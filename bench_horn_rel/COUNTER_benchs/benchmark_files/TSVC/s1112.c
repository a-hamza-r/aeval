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

TYPE s1112(int count) {
  for (int i = count*8-1; i >= 0; i--) {
    a[i] = b[i] + 1;
  }
  return 0;
}

int main() {
	return 0;
}