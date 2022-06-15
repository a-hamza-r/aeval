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

//	crossing thresholds
//	index set splitting
//	reverse data access

TYPE s281(int count) {
	int x;
	for (int i = 0; i < count*8; i+=8) {
		x = a[count*8-i-1] + b[i] * c[i];
		a[i] = x-1;
		b[i] = x;

		x = a[count*8-i+1-1] + b[i+1] * c[i+1];
		a[i+1] = x-1;
		b[i+1] = x;

		x = a[count*8-i+2-1] + b[i+2] * c[i+2];
		a[i+2] = x-1;
		b[i+2] = x;

		x = a[count*8-i+3-1] + b[i+3] * c[i+3];
		a[i+3] = x-1;
		b[i+3] = x;

		x = a[count*8-i+4-1] + b[i+4] * c[i+4];
		a[i+4] = x-1;
		b[i+4] = x;

		x = a[count*8-i+5-1] + b[i+5] * c[i+5];
		a[i+5] = x-1;
		b[i+5] = x;

		x = a[count*8-i+6-1] + b[i+6] * c[i+6];
		a[i+6] = x-1;
		b[i+6] = x;

		x = a[count*8-i+7-1] + b[i+7] * c[i+7];
		a[i+7] = x-1;
		b[i+7] = x;
	}
  return 0;
}

int main() {
	return 0;
}