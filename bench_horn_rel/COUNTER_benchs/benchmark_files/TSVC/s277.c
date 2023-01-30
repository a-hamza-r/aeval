#include "declarations.h"

//	control flow
//	test for dependences arising from guard variable computation.

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

TYPE s277(int count) {
	for (int i = 0; i < count*8-1; i++) {
		if (b[i] >= 0) {
			b[i+1] = c[i] + d[i] * e[i];
		}
	}
	return 0;
}

int main() {
	return 0;
}