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

//    control loops
//    vector assignment, gather
//    gather is required

TYPE vag(int count) {
  for (int i = 0; i < count*8; i+=8) {
    a[i] = b[ip[i]];
    a[i+1] = b[ip[i+1]];
    a[i+2] = b[ip[i+2]];
    a[i+3] = b[ip[i+3]];
    a[i+4] = b[ip[i+4]];
    a[i+5] = b[ip[i+5]];
    a[i+6] = b[ip[i+6]];
    a[i+7] = b[ip[i+7]];
  }
  return 0;
}

int main() {
  return 0;
}