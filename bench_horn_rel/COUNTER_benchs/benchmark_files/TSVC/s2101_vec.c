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

//	diagonals
//	main diagonal calculation
//	jump in data access

TYPE s2101(int count) {
	for (int i = 0; i < count*8; i+=8) {
		aa[i][i] += bb[i][i] * cc[i][i];
		aa[i+1][i+1] += bb[i+1][i+1] * cc[i+1][i+1];
		aa[i+2][i+2] += bb[i+2][i+2] * cc[i+2][i+2];
		aa[i+3][i+3] += bb[i+3][i+3] * cc[i+3][i+3];
		aa[i+4][i+4] += bb[i+4][i+4] * cc[i+4][i+4];
		aa[i+5][i+5] += bb[i+5][i+5] * cc[i+5][i+5];
		aa[i+6][i+6] += bb[i+6][i+6] * cc[i+6][i+6];
		aa[i+7][i+7] += bb[i+7][i+7] * cc[i+7][i+7];
	}
  return 0;
}

int main() {
	return 0;
}