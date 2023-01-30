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

//	loop interchange
//	loop with data dependency

TYPE s231(int count) {
	for (int j = 1; j < count*8; j++) {
		for (int i = 0; i < count*8; ++i) {
			aa[j][i] = aa[j - 1][i] + bb[j][i];
		}
	}
	return 0;
}

int main() {
	return 0;
}