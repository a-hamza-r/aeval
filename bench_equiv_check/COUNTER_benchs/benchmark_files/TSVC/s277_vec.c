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
	if (b[0] >= 0) {
		b[0+1] = c[0] + d[0] * e[0];
	}

	if (b[0+1] >= 0) {
		b[0+1+1] = c[0+1] + d[0+1] * e[0+1];
	}

	if (b[0+2] >= 0) {
		b[0+2+1] = c[0+2] + d[0+2] * e[0+2];
	}

	if (b[0+3] >= 0) {
		b[0+3+1] = c[0+3] + d[0+3] * e[0+3];
	}

	if (b[0+4] >= 0) {
		b[0+4+1] = c[0+4] + d[0+4] * e[0+4];
	}

	if (b[0+5] >= 0) {
		b[0+5+1] = c[0+5] + d[0+5] * e[0+5];
	}

	if (b[0+6] >= 0) {
		b[0+6+1] = c[0+6] + d[0+6] * e[0+6];
	}
	for (int i = 7; i < count*8-1; i+=8) {
		if (b[i] >= 0) {
			b[i+1] = c[i] + d[i] * e[i];
		}

		if (b[i+1] >= 0) {
			b[i+1+1] = c[i+1] + d[i+1] * e[i+1];
		}

		if (b[i+2] >= 0) {
			b[i+2+1] = c[i+2] + d[i+2] * e[i+2];
		}

		if (b[i+3] >= 0) {
			b[i+3+1] = c[i+3] + d[i+3] * e[i+3];
		}

		if (b[i+4] >= 0) {
			b[i+4+1] = c[i+4] + d[i+4] * e[i+4];
		}

		if (b[i+5] >= 0) {
			b[i+5+1] = c[i+5] + d[i+5] * e[i+5];
		}

		if (b[i+6] >= 0) {
			b[i+6+1] = c[i+6] + d[i+6] * e[i+6];
		}

		if (b[i+7] >= 0) {
			b[i+7+1] = c[i+7] + d[i+7] * e[i+7];
		}
	}
	return 0;
}

int main() {
	return 0;
}