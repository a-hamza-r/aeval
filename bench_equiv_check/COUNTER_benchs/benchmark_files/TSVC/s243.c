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

//	node splitting
//	false dependence cycle breaking

/*TYPE s243(int count) {
  for (int i = 0; i < count*8-1; i++) {
    a[i] = b[i] + c[i  ] * d[i];
    b[i] = a[i] + d[i  ] * e[i];
    a[i] = b[i] + a[i+1] * d[i];
  }
  return 0;
}*/

TYPE s243(int count) {
  TYPE f[count*8-1];
  for (int i = 0; i < count*8-1; i++) {
    f[i] = a[i+1];
    a[i] = b[i] + c[i  ] * d[i];
    b[i] = a[i] + d[i  ] * e[i];
    a[i] = b[i] + f[i] * d[i];
  }
  return 0;
}

int main() {
  return 0;
}