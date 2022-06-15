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

//	scalar and array expansion
//	scalar expansion

/*TYPE s1251(int count) {
  for (int i = 0; i < count*8; i++) {
    int s = b[i]+c[i];
    b[i] = a[i]+d[i];
    a[i] = s*e[i];
  }
  return 0;
}*/


TYPE s1251(int count) {
  TYPE s[count*8];
  for (int i = 0; i < count*8; i++) {
    s[i] = b[i]+c[i];
    b[i] = a[i]+d[i];
    a[i] = s[i]*e[i];
  }
  return 0;
}


int main() {
  return 0;
}