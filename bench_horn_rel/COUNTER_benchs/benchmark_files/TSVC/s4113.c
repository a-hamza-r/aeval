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
//    indirect addressing on rhs and lhs
//    gather and scatter is required

TYPE s4113(int count) {
    for (int i = 0; i < count*8; i++) {
        a[ip[i]] = b[ip[i]] + c[i];
    }
    return 0;
}

int main() {
    return 0;
}