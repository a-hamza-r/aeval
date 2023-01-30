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
	if (b[0] < 0) {
		c[0+1] = a[0] + d[0] * d[0];
	}
	else {
		a[0] = c[0] + d[0] * e[0];
	}

	if (b[0+1] < 0) {
		c[0+1+1] = a[0+1] + d[0+1] * d[0+1];
	}
	else {
		a[0+1] = c[0+1] + d[0+1] * e[0+1];
	}

	if (b[0+2] < 0) {
		c[0+2+1] = a[0+2] + d[0+2] * d[0+2];
	}
	else {
		a[0+2] = c[0+2] + d[0+2] * e[0+2];
	}

	if (b[0+3] < 0) {
		c[0+3+1] = a[0+3] + d[0+3] * d[0+3];
	}
	else {
		a[0+3] = c[0+3] + d[0+3] * e[0+3];
	}

	if (b[0+4] < 0) {
		c[0+4+1] = a[0+4] + d[0+4] * d[0+4];
	}
	else {
		a[0+4] = c[0+4] + d[0+4] * e[0+4];
	}

	if (b[0+5] < 0) {
		c[0+5+1] = a[0+5] + d[0+5] * d[0+5];
	}
	else {
		a[0+5] = c[0+5] + d[0+5] * e[0+5];
	}

	if (b[0+6] < 0) {
		c[0+6+1] = a[0+6] + d[0+6] * d[0+6];
	}
	else {
		a[0+6] = c[0+6] + d[0+6] * e[0+6];
	}
	for (int i = 7; i < count*8-1; i+=8) {
		if (b[i] < 0) {
			c[i+1] = a[i] + d[i] * d[i];
		}
		else {
			a[i] = c[i] + d[i] * e[i];
		}

		if (b[i+1] < 0) {
			c[i+1+1] = a[i+1] + d[i+1] * d[i+1];
		}
		else {
			a[i+1] = c[i+1] + d[i+1] * e[i+1];
		}

		if (b[i+2] < 0) {
			c[i+2+1] = a[i+2] + d[i+2] * d[i+2];
		}
		else {
			a[i+2] = c[i+2] + d[i+2] * e[i+2];
		}

		if (b[i+3] < 0) {
			c[i+3+1] = a[i+3] + d[i+3] * d[i+3];
		}
		else {
			a[i+3] = c[i+3] + d[i+3] * e[i+3];
		}

		if (b[i+4] < 0) {
			c[i+4+1] = a[i+4] + d[i+4] * d[i+4];
		}
		else {
			a[i+4] = c[i+4] + d[i+4] * e[i+4];
		}

		if (b[i+5] < 0) {
			c[i+5+1] = a[i+5] + d[i+5] * d[i+5];
		}
		else {
			a[i+5] = c[i+5] + d[i+5] * e[i+5];
		}

		if (b[i+6] < 0) {
			c[i+6+1] = a[i+6] + d[i+6] * d[i+6];
		}
		else {
			a[i+6] = c[i+6] + d[i+6] * e[i+6];
		}

		if (b[i+7] < 0) {
			c[i+7+1] = a[i+7] + d[i+7] * d[i+7];
		}
		else {
			a[i+7] = c[i+7] + d[i+7] * e[i+7];
		}
	}
  return 0;
}

int main() {
	return 0;
}