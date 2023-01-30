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
	for (int i = 0; i < count*8; i++) {
		a[i] = a[count*4] + b[i];
	}
  return 0;
}

int main() {
	return 0;
}