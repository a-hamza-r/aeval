#include "declarations.h"

//    indirect addressing
//    sparse dot product
//    gather is required

TYPE s4115(int count) {
if (count <= 0 || count > 10) return 1;
    TYPE sum = 0;
    for (int i = 0; i < count*8; i++) {
        sum += a[i] * b[ip[i]];
    }
    return sum;
}

