#include "declarations.h"

//    indirect addressing
//    sparse saxpy
//    gather is required

int s4112(int count, int s) {
if (count <= 0 || count > 10) return 1;
    for (int i = 0; i < count*8; i++) {
        a[i] += b[ip[i]] * s;
    }
    return 0;
}

