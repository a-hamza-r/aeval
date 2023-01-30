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
//	induction variable in two loops; collapsing possible

TYPE s125(int count) {
	for (int i = 0; i < count*8; i++) {
		for (int j = 0; j < count*8; j++) {
			array[i*count*8+j] = aa[i][j] + bb[i][j] * cc[i][j];
		}
	}
	return 0;
}

int main() {
	return 0;
}