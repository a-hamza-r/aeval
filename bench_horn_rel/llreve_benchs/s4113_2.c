#include "declarations.h"

//    indirect addressing
//    indirect addressing on rhs and lhs
//    gather and scatter is required

int s4113(int count) {
if (count <= 0 || count > 10) return 1;
    for (int i = 0; i < count*8; i+=8) {
        a[ip[i]] = b[ip[i]] + c[i];
        a[ip[i+1]] = b[ip[i+1]] + c[i+1];
        a[ip[i+2]] = b[ip[i+2]] + c[i+2];
        a[ip[i+3]] = b[ip[i+3]] + c[i+3];
        a[ip[i+4]] = b[ip[i+4]] + c[i+4];
        a[ip[i+5]] = b[ip[i+5]] + c[i+5];
        a[ip[i+6]] = b[ip[i+6]] + c[i+6];
        a[ip[i+7]] = b[ip[i+7]] + c[i+7];
    }
    return 0;
}

