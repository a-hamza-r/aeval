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

//	scalar and array expansion
//	wrap-around scalar under an if

TYPE s261(int count) {
	int t;
	for (int i = 1; i < count*8; ++i) {
		t = a[i] + b[i];
		a[i] = t + c[i-1];
		t = c[i] * d[i];
		c[i] = t;
	}
	return 0;
}

int main() {
	return 0;
}