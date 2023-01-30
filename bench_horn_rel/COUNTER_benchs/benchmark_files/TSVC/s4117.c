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

//    indirect addressing
//    seq function

TYPE s4117(int count) {
    for (int i = 0; i < count*8; i++) {
        a[i] = b[i] + c[i/2] * d[i];
    }
    return 0;
}

int main() {
	return 0;
}