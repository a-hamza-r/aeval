#include "declarations.h"

//    indirect addressing
//    mix indirect addressing with variable lower and upper bounds
//    gather is required

TYPE s4114(int count, int n1) {
    int k;
    for (int i = n1-1; i < count*8; i++) {
        k = ip[i];
        a[i] = b[i] + c[count*8-k+1-2] * d[i];
        k += 5;
    }
    return 0;
}


int nondet();

int main() {
	int count = nondet();
    int n1 = nondet();
	s4114(count, n1);
}