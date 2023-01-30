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
//	vector if/gotos

/*TYPE s279(int count) {
	for (int i = 0; i < count*8; i++) {
		if (a[i] > (float)0.) {
			goto L20;
		}
		b[i] = -b[i] + d[i] * d[i];
		if (b[i] <= a[i]) {
			goto L30;
		}
		c[i] += d[i] * e[i];
		goto L30;
L20:
		c[i] = -c[i] + e[i] * e[i];
L30:
		a[i] = b[i] + c[i] * d[i];
	}
  return 0;
}*/


TYPE s279(int count) {
	for (int i = 0; i < count*8; i++) {
		if (a[i] > 0) {
			c[i] = -c[i] + e[i] * e[i];
		}
		else {
			b[i] = -b[i] + d[i] * d[i];
			if (b[i] > a[i]) {
				c[i] += d[i] * e[i];
			}
		}
		a[i] = b[i] + c[i] * d[i];
	}
  return 0;
}

int main() {
	return 0;
}