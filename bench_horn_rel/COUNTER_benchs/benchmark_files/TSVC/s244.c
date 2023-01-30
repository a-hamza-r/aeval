#include "declarations.h"

//	node splitting
//	false dependence cycle breaking

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

TYPE s244(int count) {
	for (int i = 0; i < count*8-1; ++i) {
		a[i+1] = c[i] + b[i] + a[i+1] * d[i];
		a[i] = b[i] + c[i] * d[i];
		b[i] = c[i] + b[i];
	}
  return 0;
}

int main() {
	return 0;
}