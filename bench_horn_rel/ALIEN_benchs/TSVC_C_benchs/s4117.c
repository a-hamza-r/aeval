#include "declarations.h"

//    indirect addressing
//    seq function

TYPE s4117(int count) {
    for (int i = 0; i < count*8; i++) {
        a[i] = b[i] + c[i/2] * d[i];
    }
    return 0;
}


int nondet();

int main() {
	int count = nondet();
	s4117(count);
}