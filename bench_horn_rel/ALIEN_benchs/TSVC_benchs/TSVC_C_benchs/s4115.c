#include "declarations.h"

//    indirect addressing
//    sparse dot product
//    gather is required

TYPE s4115(int count) {
    TYPE sum = 0;
    for (int i = 0; i < count*8; i++) {
        sum += a[i] * b[ip[i]];
    }
    return sum;
}


int nondet();

int main() {
	int count = nondet();
	s4115(count);
}