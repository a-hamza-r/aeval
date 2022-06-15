#include "declarations.h"

//    vector semantics
//    indirect addressing on lhs, store in sequence
//    scatter is required

int s491(int count) {
if (count <= 0 || count > 10) return 1;
    for (int i = 0; i < count*8; i++) {
        a[ip[i]] = b[i] + c[i] * d[i];
    }
    return 0;
}

