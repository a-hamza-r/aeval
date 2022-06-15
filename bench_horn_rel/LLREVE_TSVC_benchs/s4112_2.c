#include "declarations.h"

//    indirect addressing
//    sparse saxpy
//    gather is required

int s4112(int count, int s) {
if (count <= 0 || count > 10) return 1;
    for (int i = 0; i < count*8; i+=8) {
        a[i] += b[ip[i]] * s;
        a[i+1] += b[ip[i+1]] * s;
        a[i+2] += b[ip[i+2]] * s;
        a[i+3] += b[ip[i+3]] * s;
        a[i+4] += b[ip[i+4]] * s;
        a[i+5] += b[ip[i+5]] * s;
        a[i+6] += b[ip[i+6]] * s;
        a[i+7] += b[ip[i+7]] * s;
    }
    return 0;
}

