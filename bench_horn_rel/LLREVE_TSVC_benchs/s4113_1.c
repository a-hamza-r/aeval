#include "declarations.h"

//    indirect addressing
//    indirect addressing on rhs and lhs
//    gather and scatter is required

int s4113(int count) {
if (count <= 0 || count > 10) return 1;
    for (int i = 0; i < count*8; i++) {
        a[ip[i]] = b[ip[i]] + c[i];
    }
    return 0;
}

