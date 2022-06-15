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
//	induction variable in two loops; recurrence in inner loop

TYPE s126(int count) {
	for (int j = 1; j < count*8; j++) {
		for (int i = 0; i < count*8; i+=8) {
			bb[j][i] = bb[j-1][i] + array[i+j-1] * cc[j][i];
			bb[j][i+1] = bb[j-1][i+1] + array[i+1+j-1] * cc[j][i+1];
			bb[j][i+2] = bb[j-1][i+2] + array[i+2+j-1] * cc[j][i+2];
			bb[j][i+3] = bb[j-1][i+3] + array[i+3+j-1] * cc[j][i+3];
			bb[j][i+4] = bb[j-1][i+4] + array[i+4+j-1] * cc[j][i+4];
			bb[j][i+5] = bb[j-1][i+5] + array[i+5+j-1] * cc[j][i+5];
			bb[j][i+6] = bb[j-1][i+6] + array[i+6+j-1] * cc[j][i+6];
			bb[j][i+7] = bb[j-1][i+7] + array[i+7+j-1] * cc[j][i+7];
		}
	}
	return 0;
}

int main() {
	return 0;
}