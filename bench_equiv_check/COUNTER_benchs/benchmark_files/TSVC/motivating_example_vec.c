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

TYPE motivating_example(int count) {
  a[0] = a[0+1] + b[0];
  a[1] = a[1+1] + b[1];
  for (int i = 2; i < count*4-2; i+=4) {
    a[i] = a[i+1] + b[i];
    a[i+1] = a[i+1+1] + b[i+1];
    a[i+2] = a[i+2+1] + b[i+2];
    a[i+3] = a[i+3+1] + b[i+3];
  }
  a[count*4-2] = a[count*4-1] + b[count*4-2];
  return 0;
}

int main() {
  return 0;
}
