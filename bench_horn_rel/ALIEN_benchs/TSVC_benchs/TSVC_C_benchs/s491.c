#include "declarations.h"

//    vector semantics
//    indirect addressing on lhs, store in sequence
//    scatter is required

TYPE s491(int count) {
    for (int i = 0; i < count*8; i++) {
        a[ip[i]] = b[i] + c[i] * d[i];
    }
    return 0;
}


int nondet();

int main() {
	int count = nondet();
	s491(count);
}