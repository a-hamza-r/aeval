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
//	tests for recognition of loop independent dependences
//	between statements in mutually exclusive regions.

TYPE s161(int count) {
	for (int i = 0; i < count*8-1; ++i) {
		if (b[i] < 0) {
			c[i+1] = a[i] + d[i] * d[i];
		}
		else {
			a[i] = c[i] + d[i] * e[i];
		}
	}
  return 0;
}

int main() {
	return 0;
}