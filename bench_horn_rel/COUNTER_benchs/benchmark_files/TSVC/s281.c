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
	for (int i = 0; i < count*8; i++) {
		x = a[count*8-i-1] + b[i] * c[i];
		a[i] = x-1;
		b[i] = x;
	}
  return 0;
}

int main() {
	return 0;
}