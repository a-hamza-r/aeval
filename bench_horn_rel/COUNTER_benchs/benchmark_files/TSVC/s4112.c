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
//    sparse saxpy
//    gather is required

TYPE s4112(int count, TYPE s) {
    for (int i = 0; i < count*8; i++) {
        a[i] += b[ip[i]] * s;
    }
    return 0;
}

int main() {
    return 0;
}