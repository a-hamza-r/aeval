#include "declarations.h"

//    indirect addressing
//    sparse saxpy
//    gather is required

TYPE s4112(int count) {
    for (int i = 0; i < count*8; i++) {
        a[i] += b[ip[i]] * s;
    }
    return 0;
}


int nondet();

int main() {
	int count = nondet();
	s4112(count);
}