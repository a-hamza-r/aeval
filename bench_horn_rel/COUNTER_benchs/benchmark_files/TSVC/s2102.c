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
//	identity matrix, best results vectorize both inner and outer loops

TYPE s2102(int count) {
	for (int j = 0; j < count*8; j++) {
		for (int i = 0; i < count*8; i++) {
			aa[j][i] = 0;
		}
		aa[j][j] = 1;
	}
  return 0;
}

int main() {
	return 0;
}