#include "declarations.h"

//	statement reordering
//	dependency needing temporary

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

TYPE s212(int count) {
	for (int i = 0; i < count*8-1; i++) {
		b[i] += a[i + 1] * d[i];
		a[i] *= c[i];
	}
  return 0;
}

int main() {
	return 0;
}