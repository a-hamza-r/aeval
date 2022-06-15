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

//	induction variables
//	coupled induction variables
//	jump in data access


TYPE s128(int count) {
	for (int i = 0; i < count*4; i+=4) {
		a[i] = b[2*i] - d[i];
		b[2*i] = a[i] + c[2*i];

		a[(i+1)] = b[2*(i+1)] - d[(i+1)];
		b[2*(i+1)] = a[(i+1)] + c[2*(i+1)];

		a[(i+2)] = b[2*(i+2)] - d[(i+2)];
		b[2*(i+2)] = a[(i+2)] + c[2*(i+2)];

		a[(i+3)] = b[2*(i+3)] - d[(i+3)];
		b[2*(i+3)] = a[(i+3)] + c[2*(i+3)];
	}
  return 0;
}

int main() {
	return 0;
}