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

//	induction variable recognition
//	variable lower and upper bound, and stride
//	reverse data access and jump in data access

TYPE s122(int count) {
  // int k = 0;
  for (int i = 1; i < count*8; i++) {
    // k++;
    // a[i] += b[count*8-k];
    a[i] += b[count*8-i];
  }
  return 0;
}

int main() {
	return 0;
}