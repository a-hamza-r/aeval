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
		for (int i = 0; i < count*8; i++) {
			cc[j][i] = a[j] + bb[j][i]*d[j];
	 }
	}
	return 0;
}

int main() {
	return 0;
}