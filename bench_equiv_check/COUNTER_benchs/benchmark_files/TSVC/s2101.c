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
	for (int i = 0; i < count*8; i++) {
		aa[i][i] += bb[i][i] * cc[i][i];
	}
  return 0;
}

int main() {
	return 0;
}