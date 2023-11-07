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
//	loop with singularity handling

TYPE s271(int count) {
	for (int i = 0; i < count*8; i++) {
		if (b[i] > 0) {
			a[i] += b[i] * c[i];
		}
	}
  return 0;
}

int main() {
	return 0;
}