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

TYPE vsumr(int count) {
  TYPE sum = 0;
  for (int i = 0; i < count*8; i++) {
    sum += a[i];
  }
  return sum;
}


int main() {
	return 0;
}