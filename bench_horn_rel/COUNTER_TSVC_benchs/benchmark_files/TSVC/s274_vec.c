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
	for (int i = 0; i < count*8; i+=8) {
		a[i] = c[i] + e[i] * d[i];
		if (a[i] > 0) {
			b[i] = a[i] + b[i];
		} else {
			a[i] = d[i] * e[i];
		}

		a[i+1] = c[i+1] + e[i+1] * d[i+1];
		if (a[i+1] > 0) {
			b[i+1] = a[i+1] + b[i+1];
		} else {
			a[i+1] = d[i+1] * e[i+1];
		}

		a[i+2] = c[i+2] + e[i+2] * d[i+2];
		if (a[i+2] > 0) {
			b[i+2] = a[i+2] + b[i+2];
		} else {
			a[i+2] = d[i+2] * e[i+2];
		}

		a[i+3] = c[i+3] + e[i+3] * d[i+3];
		if (a[i+3] > 0) {
			b[i+3] = a[i+3] + b[i+3];
		} else {
			a[i+3] = d[i+3] * e[i+3];
		}

		a[i+4] = c[i+4] + e[i+4] * d[i+4];
		if (a[i+4] > 0) {
			b[i+4] = a[i+4] + b[i+4];
		} else {
			a[i+4] = d[i+4] * e[i+4];
		}

		a[i+5] = c[i+5] + e[i+5] * d[i+5];
		if (a[i+5] > 0) {
			b[i+5] = a[i+5] + b[i+5];
		} else {
			a[i+5] = d[i+5] * e[i+5];
		}

		a[i+6] = c[i+6] + e[i+6] * d[i+6];
		if (a[i+6] > 0) {
			b[i+6] = a[i+6] + b[i+6];
		} else {
			a[i+6] = d[i+6] * e[i+6];
		}

		a[i+7] = c[i+7] + e[i+7] * d[i+7];
		if (a[i+7] > 0) {
			b[i+7] = a[i+7] + b[i+7];
		} else {
			a[i+7] = d[i+7] * e[i+7];
		}
	}
	return 0;
}

int main() {
	return 0;
}