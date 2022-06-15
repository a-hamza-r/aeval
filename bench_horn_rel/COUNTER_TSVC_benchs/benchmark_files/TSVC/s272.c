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
//	loop with independent conditional

TYPE s272(int count, int t) {
	for (int i = 0; i < count*8; i++) {
		if (e[i] >= t) {
			a[i] += c[i] * d[i];
			b[i] += c[i] * c[i];
		}
	}
	return 0;
}


int main() {
	return 0;
}