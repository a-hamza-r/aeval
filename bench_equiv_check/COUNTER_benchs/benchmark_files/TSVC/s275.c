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

//	control flow
//	if around inner loop, interchanging needed

TYPE s275(int count) {
	for (int j = 1; j < count*8; j++) {
		for (int i = 0; i < count*8; i++) {
			if (aa[0][i] > 0) {
				aa[j][i] = aa[j-1][i] + bb[j][i] * cc[j][i];
			}
		}
	}
  return 0;
}

int main() {
	return 0;
}