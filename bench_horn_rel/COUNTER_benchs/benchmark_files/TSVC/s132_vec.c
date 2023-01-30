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

//	global data flow analysis
//	loop with multiple dimension ambiguous subscripts

TYPE s132(int count) {
	aa[0][1] = aa[1][1-1] + b[1] * c[1];
	aa[0][1+1] = aa[1][1+1-1] + b[1+1] * c[1];
	aa[0][1+2] = aa[1][1+2-1] + b[1+2] * c[1];
	aa[0][1+3] = aa[1][1+3-1] + b[1+3] * c[1];
	aa[0][1+4] = aa[1][1+4-1] + b[1+4] * c[1];
	aa[0][1+5] = aa[1][1+5-1] + b[1+5] * c[1];
	aa[0][1+6] = aa[1][1+6-1] + b[1+6] * c[1];
	for (int i=8; i < count*8; i+=8) {
		aa[0][i] = aa[1][i-1] + b[i] * c[1];
		aa[0][i+1] = aa[1][i+1-1] + b[i+1] * c[1];
		aa[0][i+2] = aa[1][i+2-1] + b[i+2] * c[1];
		aa[0][i+3] = aa[1][i+3-1] + b[i+3] * c[1];
		aa[0][i+4] = aa[1][i+4-1] + b[i+4] * c[1];
		aa[0][i+5] = aa[1][i+5-1] + b[i+5] * c[1];
		aa[0][i+6] = aa[1][i+6-1] + b[i+6] * c[1];
		aa[0][i+7] = aa[1][i+7-1] + b[i+7] * c[1];
	}
  return 0;
}

int main() {
	return 0;
}