#include "declarations.h"

//	statement reordering
//	statement reordering allows vectorization

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

TYPE s211(int count) {
	for (int i = 1; i < count*8-1; i++) {
		b[i] = b[i + 1] - e[i] * d[i];
		a[i] = b[i - 1] + c[i] * d[i];
	}
	return 0;
}

int main() {
	return 0;
}