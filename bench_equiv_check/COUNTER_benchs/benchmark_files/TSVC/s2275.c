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

//	loop distribution is needed to be able to interchange

TYPE s2275(int count) {
	for (int j = 0; j < count*8; j++) {
		for (int i = 0; i < count*8; i++) {
			aa[j][i] = aa[j][i] + bb[j][i] * cc[j][i];
		}
		a[j] = b[j] + c[j] * d[j];
	}
  return 0;
}

int main() {
	return 0;
}