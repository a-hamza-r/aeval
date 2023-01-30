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

//	node splitting
//	cycle with ture and anti dependency

TYPE s1244(int count) {
	TYPE t = a[0+1];
	a[0] = b[0] + c[0] * c[0] + b[0]*b[0] + c[0];
	d[0] = a[0] + t;

	t = a[0+1+1];
	a[0+1] = b[0+1] + c[0+1] * c[0+1] + b[0+1]*b[0+1] + c[0+1];
	d[0+1] = a[0+1] + t;

	t = a[0+2+1];
	a[0+2] = b[0+2] + c[0+2] * c[0+2] + b[0+2]*b[0+2] + c[0+2];
	d[0+2] = a[0+2] + t;

	t = a[0+3+1];
	a[0+3] = b[0+3] + c[0+3] * c[0+3] + b[0+3]*b[0+3] + c[0+3];
	d[0+3] = a[0+3] + t;

	t = a[0+4+1];
	a[0+4] = b[0+4] + c[0+4] * c[0+4] + b[0+4]*b[0+4] + c[0+4];
	d[0+4] = a[0+4] + t;

	t = a[0+5+1];
	a[0+5] = b[0+5] + c[0+5] * c[0+5] + b[0+5]*b[0+5] + c[0+5];
	d[0+5] = a[0+5] + t;

	t = a[0+6+1];
	a[0+6] = b[0+6] + c[0+6] * c[0+6] + b[0+6]*b[0+6] + c[0+6];
	d[0+6] = a[0+6] + t;

	for (int i = 7; i < count*8-1; i+=8) {
		TYPE t = a[i+1];
		a[i] = b[i] + c[i] * c[i] + b[i]*b[i] + c[i];
		d[i] = a[i] + t;

		t = a[i+1+1];
		a[i+1] = b[i+1] + c[i+1] * c[i+1] + b[i+1]*b[i+1] + c[i+1];
		d[i+1] = a[i+1] + t;

		t = a[i+2+1];
		a[i+2] = b[i+2] + c[i+2] * c[i+2] + b[i+2]*b[i+2] + c[i+2];
		d[i+2] = a[i+2] + t;

		t = a[i+3+1];
		a[i+3] = b[i+3] + c[i+3] * c[i+3] + b[i+3]*b[i+3] + c[i+3];
		d[i+3] = a[i+3] + t;

		t = a[i+4+1];
		a[i+4] = b[i+4] + c[i+4] * c[i+4] + b[i+4]*b[i+4] + c[i+4];
		d[i+4] = a[i+4] + t;

		t = a[i+5+1];
		a[i+5] = b[i+5] + c[i+5] * c[i+5] + b[i+5]*b[i+5] + c[i+5];
		d[i+5] = a[i+5] + t;

		t = a[i+6+1];
		a[i+6] = b[i+6] + c[i+6] * c[i+6] + b[i+6]*b[i+6] + c[i+6];
		d[i+6] = a[i+6] + t;

		t = a[i+7+1];
		a[i+7] = b[i+7] + c[i+7] * c[i+7] + b[i+7]*b[i+7] + c[i+7];
		d[i+7] = a[i+7] + t;
	}
  return 0;
}

int main() {
	return 0;
}