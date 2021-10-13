#include "declarations.h"

//    indirect addressing
//    seq function

int s4117(int count) {
if (count <= 0 || count > 10) return 1;
    for (int i = 0; i < count*8; i++) {
        a[i] = b[i] + c[i/2] * d[i];
    }
    return 0;
}

