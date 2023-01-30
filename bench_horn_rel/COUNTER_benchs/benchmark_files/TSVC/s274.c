#include "declarations.h"

//	control flow
//	complex loop with dependent conditional

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

TYPE s274(int count) {
	for (int i = 0; i < count*8; i++) {
		a[i] = c[i] + e[i] * d[i];
		if (a[i] > (float)0.) {
			b[i] = a[i] + b[i];
		} else {
			a[i] = d[i] * e[i];
		}
	}
	return 0;
}

int main() {
	return 0;
}