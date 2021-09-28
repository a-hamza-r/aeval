#include "declarations.h"

//    indirect addressing
//    more complicated sparse sdot
//    gather is required

TYPE s4116(int count, int j) {
    TYPE sum = 0;
    for (int i = 0; i < count*8-1; i++) {
        off = inc + i;
        sum += a[off] * aa[j-1][ip[i]];
    }
    return 0;
}


int nondet();

int main() {
	int count = nondet();
    int j = nondet();
	s4116(count, j);
}