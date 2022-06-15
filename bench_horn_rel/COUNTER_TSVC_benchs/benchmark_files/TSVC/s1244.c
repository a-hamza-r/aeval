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

//	node splitting
//	cycle with ture and anti dependency

/*TYPE s1244(int count) {
	for (int i = 0; i < count*8-1; i++) {
		a[i] = b[i] + c[i] * c[i] + b[i]*b[i] + c[i];
		d[i] = a[i] + a[i+1];
	}
  return 0;
}*/

TYPE s1244(int count) {
	for (int i = 0; i < count*8-1; i++) {
		TYPE t = a[i+1];
		a[i] = b[i] + c[i] * c[i] + b[i]*b[i] + c[i];
		d[i] = a[i] + t;
	}
  return 0;
}

int main() {
	return 0;
}