#include "declarations.h"

//	scalar and array expansion
//	scalar expansion assigned under if

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

TYPE s253(int count) {
	int s[count*8];
	for (int i = 0; i < count*8; i++) {
		if (a[i] > b[i]) {
			s[i] = a[i] - b[i] * d[i];
			c[i] += s[i];
			a[i] = s[i];
		}
	}
  return 0;
}

int main() {
	return 0;
}