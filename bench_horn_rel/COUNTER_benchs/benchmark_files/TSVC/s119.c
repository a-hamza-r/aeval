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

//	linear dependence testing
//	no dependence - vectorizable

TYPE s119(int count) {
	for (int i = 1; i < count*8; i++) {
		for (int j = 1; j < count*8; j++) {
			aa[i][j] = aa[i-1][j-1] + bb[i][j];
		}
	}
	return 0;
}

int main() {
	return 0;
}