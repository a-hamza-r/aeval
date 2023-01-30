#include "declarations.h"

//    non-logical if's
//    arithmetic if

TYPE s443(int count) {
    for (int i = 0; i < count*8; i++) {
        if (d[i] <= 0) {
            a[i] += b[i] * c[i];
        } else {
            a[i] += b[i] * b[i];
        }
    }
    return 0;
}


int nondet();

int main() {
	int count = nondet();
	s443(count);
}