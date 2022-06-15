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

//	linear dependence testing
//	one iteration dependency on a(count*4) but still vectorizable

TYPE s1113(int count) {
	for (int i = 0; i < count*8; i+=8) {
		a[i] = a[count*4] + b[i];
		a[i+1] = a[count*4] + b[i+1];
		a[i+2] = a[count*4] + b[i+2];
		a[i+3] = a[count*4] + b[i+3];
		a[i+4] = a[count*4] + b[i+4];
		a[i+5] = a[count*4] + b[i+5];
		a[i+6] = a[count*4] + b[i+6];
		a[i+7] = a[count*4] + b[i+7];
	}
  return 0;
}

int main() {
	return 0;
}