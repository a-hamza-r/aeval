#include "declarations.h"

//    indirect addressing
//    indirect addressing on rhs and lhs
//    gather and scatter is required

TYPE s4113(int count) {
    for (int i = 0; i < count*8; i++) {
        a[ip[i]] = b[ip[i]] + c[i];
    }
    return 0;
}


int nondet();

int main() {
	int count = nondet();
	s4113(count);
}