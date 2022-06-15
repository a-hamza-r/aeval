#include "declarations.h"

//  induction variable recognition
//  induction variable with multiple increments

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

/*TYPE s127(int count) {
  int j = -1;
  for (int i = 0; i < count*4-1; i++) {
    j++;
    a[j] = b[i] + c[i] * d[i];
    j++;
    a[j] = b[i] + d[i] * e[i];
  }
  return 0;
}*/

TYPE s127(int count) {
  for (int i = 0; i < count*4-1; i++) {
    a[2*i] = b[i] + c[i] * d[i];
    a[2*i+1] = b[i] + d[i] * e[i];
  }
  return 0;
}

int main() {
  return 0;
}