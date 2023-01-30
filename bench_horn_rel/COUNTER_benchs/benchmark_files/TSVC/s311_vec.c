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

TYPE s311(int count) {
  TYPE sum = 0;
  for (int i = 0; i < count*8; i+=8) {
    sum += a[i];
    sum += a[i+1];
    sum += a[i+2];
    sum += a[i+3];
    sum += a[i+4];
    sum += a[i+5];
    sum += a[i+6];
    sum += a[i+7];
  }
  return sum;
}

int main() {
	return 0;
}