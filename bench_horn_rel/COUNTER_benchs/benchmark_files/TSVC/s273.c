#include "declarations.h"

//	control flow
//	simple loop with dependent conditional

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

TYPE s273(int count) {
	for (int i = 0; i < count*8; i++) {
		a[i] += d[i] * e[i];
		if (a[i] < 0)
			b[i] += d[i] * e[i];
		c[i] += a[i] * d[i];
	}
	return 0;
}

int main() {
	return 0;
}