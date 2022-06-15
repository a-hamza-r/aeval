#include "declarations.h"

//    indirect addressing
//    seq function

TYPE 
__attribute__((noinline))
s4117(TYPE* a, TYPE* b, TYPE *c, TYPE *d, int count) {
    for (int i = 0; i < count*8; i++) {
        a[i] = b[i] + c[i/2] * d[i];
    }
    return 0;
}

TYPE 
__attribute__((noinline))
s4117_vec(TYPE* a, TYPE* b, TYPE *c, TYPE *d, int count) {
    for (int i = 0; i < count*8; i+=8) {
        a[i] = b[i] + c[i/2] * d[i];
        a[(i+1)] = b[(i+1)] + c[(i+1)/2] * d[(i+1)];
        a[(i+2)] = b[(i+2)] + c[(i+2)/2] * d[(i+2)];
        a[(i+3)] = b[(i+3)] + c[(i+3)/2] * d[(i+3)];
        a[(i+4)] = b[(i+4)] + c[(i+4)/2] * d[(i+4)];
        a[(i+5)] = b[(i+5)] + c[(i+5)/2] * d[(i+5)];
        a[(i+6)] = b[(i+6)] + c[(i+6)/2] * d[(i+6)];
        a[(i+7)] = b[(i+7)] + c[(i+7)/2] * d[(i+7)];
    }
    return 0;
}

int main() {
    return 0;
}