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
  a[1] += b[count*8-1];
  a[2] += b[count*8-2];
  a[3] += b[count*8-3];
  a[4] += b[count*8-4];
  a[5] += b[count*8-5];
  a[6] += b[count*8-6];
  a[7] += b[count*8-7];
  for (int i = 8; i < count*8; i+=8) {
    a[i] += b[count*8-i];
    a[(i+1)] += b[count*8-(i+1)];
    a[(i+2)] += b[count*8-(i+2)];
    a[(i+3)] += b[count*8-(i+3)];
    a[(i+4)] += b[count*8-(i+4)];
    a[(i+5)] += b[count*8-(i+5)];
    a[(i+6)] += b[count*8-(i+6)];
    a[(i+7)] += b[count*8-(i+7)];
  }
  return 0;
}

int main() {
	return 0;
}