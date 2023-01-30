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

//	statement reordering
//	dependency needing temporary

/*TYPE s1213(int count) {
	for (int i = 1; i < count*8-1; i++) {
		a[i] = b[i-1]+c[i];
		b[i] = a[i+1]*d[i];
	}
  return 0;
}*/


TYPE s1213(int count) {
	for (int i = 1; i < count*8-1; i++) {
		b[i] = a[i+1]*d[i];
		a[i] = b[i-1]+c[i];
	}
  return 0;
}

int main() {
	return 0;
}