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
		for (int i = 0; i < count*8; i++) {
			bb[j][i] = bb[j-1][i] + array[i+j-1] * cc[j][i];
		}
	}
	return 0;
}

int main() {
	return 0;
}