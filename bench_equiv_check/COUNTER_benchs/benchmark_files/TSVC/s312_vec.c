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

TYPE s312(int count) {
	TYPE prod = 1;
	for (int i = 0; i < count*8; i+=8) {
		prod *= a[i];
		prod *= a[i+1];
		prod *= a[i+2];
		prod *= a[i+3];
		prod *= a[i+4];
		prod *= a[i+5];
		prod *= a[i+6];
		prod *= a[i+7];
	}
	return prod;
}

int main() {
	return 0;
}