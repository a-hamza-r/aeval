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
//	preloading necessary to allow vectorization

TYPE s241(int count) {
	TYPE e[count*8-1];
	for (int i = 0; i < count*8-1; i++) {
		e[i] = a[i+1];
		a[i] = b[i] * c[i  ] * d[i];
		b[i] = a[i] * e[i] * d[i];
	}
	return 0;
}

int main() {
	return 0;
}