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

//	induction variables
//	coupled induction variables
//	jump in data access

/*TYPE s128(int count) {
	int j = -1, k;
	for (int i = 0; i < count*4; i++) {
		k = j + 1;
		a[i] = b[k] - d[i];
		j = k + 1;
		b[k] = a[i] + c[k];
	}
  return 0;
}*/

TYPE s128(int count) {
	for (int i = 0; i < count*4; i++) {
		a[i] = b[2*i] - d[i];
		b[2*i] = a[i] + c[2*i];
	}
  return 0;
}

int main() {
	return 0;
}