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

TYPE s1119(int count) {
	for (int i = 1; i < count*8; i++) {
		for (int j = 0; j < count*8; j+=8) {
			aa[i][j] = aa[i-1][j] + bb[i][j];
			aa[i][j+1] = aa[i-1][j+1] + bb[i][j+1];
			aa[i][j+2] = aa[i-1][j+2] + bb[i][j+2];
			aa[i][j+3] = aa[i-1][j+3] + bb[i][j+3];
			aa[i][j+4] = aa[i-1][j+4] + bb[i][j+4];
			aa[i][j+5] = aa[i-1][j+5] + bb[i][j+5];
			aa[i][j+6] = aa[i-1][j+6] + bb[i][j+6];
			aa[i][j+7] = aa[i-1][j+7] + bb[i][j+7];
		}
	}
	return 0;
}

int main() {
	return 0;
}