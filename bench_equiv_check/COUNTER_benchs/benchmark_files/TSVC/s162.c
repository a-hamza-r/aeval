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

//	control flow
//	deriving assertions

TYPE s162(int count, int k) {
  if (k > 0) {
    for (int i = 0; i < count*8-1; i++) {
      a[i] = a[i + k] + b[i] * c[i];
    }
  }
  return 0;
}

int main() {
	return 0;
}