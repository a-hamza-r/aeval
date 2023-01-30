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

//	global data flow analysis
//	forward substitution

/*TYPE s131(int count) {
	int m = 1;
	for (int i = 0; i < count*8 - 1; i++) {
		a[i] = a[i + m] + b[i];
	}
	return 0;
}*/

TYPE s131(int count) {
	for (int i = 0; i < count*8 - 1; i++) {
		a[i] = a[i + 1] + b[i];
	}
	return 0;
}

int main() {
	return 0;
}