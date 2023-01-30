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

TYPE s319(int count) {
  TYPE sum = 0;
  for (int i = 0; i < count*8; i++) {
      a[i] = c[i] + d[i];
      sum += a[i];
      b[i] = c[i] + e[i];
      sum += b[i];
  }
  return sum;
}

int main() {
	return 0;
}