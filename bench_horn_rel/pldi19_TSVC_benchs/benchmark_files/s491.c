#include "declarations.h"

//    vector semantics
//    indirect addressing on lhs, store in sequence
//    scatter is required

TYPE 
__attribute__((noinline))
s491(TYPE* a, TYPE* b, TYPE *c, TYPE *d, int *ip, int count) {
    for (int i = 0; i < count*8; i++) {
        a[ip[i]] = b[i] + c[i] * d[i];
    }
    return 0;
}

TYPE 
__attribute__((noinline))
s491_vec(TYPE* a, TYPE* b, TYPE *c, TYPE *d, int *ip, int count) {
    for (int i = 0; i < count*8; i+=8) {
        a[ip[i]] = b[i] + c[i] * d[i];
        a[ip[i+1]] = b[i+1] + c[i+1] * d[i+1];
        a[ip[i+2]] = b[i+2] + c[i+2] * d[i+2];
        a[ip[i+3]] = b[i+3] + c[i+3] * d[i+3];
        a[ip[i+4]] = b[i+4] + c[i+4] * d[i+4];
        a[ip[i+5]] = b[i+5] + c[i+5] * d[i+5];
        a[ip[i+6]] = b[i+6] + c[i+6] * d[i+6];
        a[ip[i+7]] = b[i+7] + c[i+7] * d[i+7];
    }
    return 0;
}

int main() {
    return 0;
}