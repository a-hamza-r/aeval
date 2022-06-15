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
	for (int i=1; i < count*8; i++) {
		aa[0][i] = aa[1][i-1] + b[i] * c[1];
	}
  return 0;
}

int main() {
	return 0;
}