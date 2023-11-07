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

//    non-logical if's
//    arithmetic if

TYPE s443(int count) {
    for (int i = 0; i < count*8; i++) {
        if (d[i] <= 0) {
            a[i] += b[i] * c[i];
        } else {
            a[i] += b[i] * b[i];
        }
    }
    return 0;
}

int main() {
    return 0;
}