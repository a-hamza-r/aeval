#include "declarations.h"

//	control flow
//	if test using loop index

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

TYPE s276(int count, int mid) {
	for (int i = 0; i < count*8; i++) {
		if (i+1 < mid) {
			a[i] += b[i] * c[i];
		} else {
			a[i] += b[i] * d[i];
		}
	}
	return 0;
}

int main() {
	return 0;
}