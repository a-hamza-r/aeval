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
//    more complicated sparse sdot
//    gather is required

TYPE s4116(int count, int j, int inc) {
    int off;
    TYPE sum = 0;
    for (int i = 0; i < count*8-1; i++) {
        off = inc + i;
        sum += a[off] * aa[j-1][ip[i]];
    }
    return 0;
}

int main() {
    return 0;
}