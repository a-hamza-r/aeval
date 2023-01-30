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

//	scalar and array expansion
//	array expansion

TYPE s256(int count) {
	for (int j = 1; j < count*8; j++) {
		a[j] = 1 - a[j - 1];
		for (int i = 0; i < count*8; i+=8) {
			cc[j][i] = a[j] + bb[j][i]*d[j];
			cc[j][i+1] = a[j] + bb[j][i+1]*d[j];
			cc[j][i+2] = a[j] + bb[j][i+2]*d[j];
			cc[j][i+3] = a[j] + bb[j][i+3]*d[j];
			cc[j][i+4] = a[j] + bb[j][i+4]*d[j];
			cc[j][i+5] = a[j] + bb[j][i+5]*d[j];
			cc[j][i+6] = a[j] + bb[j][i+6]*d[j];
			cc[j][i+7] = a[j] + bb[j][i+7]*d[j];
	 	}
	}
	return 0;
}

int main() {
	return 0;
}