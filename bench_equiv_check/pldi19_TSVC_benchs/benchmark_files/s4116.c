#include "declarations.h"

//    indirect addressing
//    more complicated sparse sdot
//    gather is required

TYPE 
__attribute__((noinline))
s4116(TYPE** aa, TYPE* a, int *ip, int count, int j, int inc) {
    int off;
    TYPE sum = 0;
    for (int i = 0; i < count*8-1; i++) {
        off = inc + i;
        sum += a[off] * aa[j-1][ip[i]];
    }
    return 0;
}

TYPE 
__attribute__((noinline))
s4116_vec(TYPE** aa, TYPE* a, int *ip, int count, int j, int inc) {
    int off;
    TYPE sum = 0;
    if (count > 0) {
    off = inc + 0;
    sum += a[off] * aa[j-1][ip[0]];

    off = inc + 0+1;
    sum += a[off] * aa[j-1][ip[0+1]];

    off = inc + 0+2;
    sum += a[off] * aa[j-1][ip[0+2]];

    off = inc + 0+3;
    sum += a[off] * aa[j-1][ip[0+3]];

    off = inc + 0+4;
    sum += a[off] * aa[j-1][ip[0+4]];

    off = inc + 0+5;
    sum += a[off] * aa[j-1][ip[0+5]];

    off = inc + 0+6;
    sum += a[off] * aa[j-1][ip[0+6]];
}

    for (int i = 7; i < count*8-1; i+=8) {
        off = inc + i;
        sum += a[off] * aa[j-1][ip[i]];

        off = inc + i+1;
        sum += a[off] * aa[j-1][ip[i+1]];

        off = inc + i+2;
        sum += a[off] * aa[j-1][ip[i+2]];

        off = inc + i+3;
        sum += a[off] * aa[j-1][ip[i+3]];

        off = inc + i+4;
        sum += a[off] * aa[j-1][ip[i+4]];

        off = inc + i+5;
        sum += a[off] * aa[j-1][ip[i+5]];

        off = inc + i+6;
        sum += a[off] * aa[j-1][ip[i+6]];

        off = inc + i+7;
        sum += a[off] * aa[j-1][ip[i+7]];
    }
    return 0;
}

int main() {
	return 0;
}