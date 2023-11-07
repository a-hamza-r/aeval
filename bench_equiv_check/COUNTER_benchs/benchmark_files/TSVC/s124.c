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

//	induction variable recognition
//	induction variable under both sides of if (same value)

/*TYPE s124(int count) {
	int j = -1;
	for (int i = 0; i < count*8; i++) {
		if (b[i] > (float)0.) {
			j++;
			a[j] = b[i] + d[i] * e[i];
		} else {
			j++;
			a[j] = c[i] + d[i] * e[i];
		}
	}
	return 0;
}*/


TYPE s124(int count) {
	for (int i = 0; i < count*8; i++) {
		if (b[i] > 0) {
			a[i] = b[i] + d[i] * e[i];
		} else {
			a[i] = c[i] + d[i] * e[i];
		}
	}
	return 0;
}

int main() {
	return 0;
}