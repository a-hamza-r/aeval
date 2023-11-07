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
	for (int i = 0; i < count*8; i++) {
		prod *= a[i];
	}
	return prod;
}

int main() {
	return 0;
}