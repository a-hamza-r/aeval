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

//	run-time symbolic resolution

TYPE s1221(int count) {
  for (int i = 4; i < count*8; i+=4) {
    a[i] = a[i-4] + b[i];
    a[i+1] = a[i-3] + b[i+1];
    a[i+2] = a[i-2] + b[i+2];
    a[i+3] = a[i-1] + b[i+3];
  }
  return 0;
}

int main() {
  return 0;
}