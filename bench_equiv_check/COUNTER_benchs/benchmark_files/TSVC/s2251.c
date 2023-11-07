#include "declarations.h"

//	scalar and array expansion
//	scalar expansion

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

TYPE s2251(int count) {
	int s[count*8+1];
	s[0] = 0;
	for (int i = 0; i < count*8; i++) {
		a[i] = s[i]*e[i];
		s[i+1] = b[i]+c[i];
		b[i] = a[i]+d[i];
	}
	return 0;
}

int main() {
	return 0;
}