#include "declarations.h"

//    control flow
//    tests for recognition of loop independent dependences
//    between statements in mutually exclusive regions.

TYPE s1161(int count)
{
    for (int i = 0; i < count*8-1; ++i) {
        if (c[i] < (float)0.) {
            goto L20;
        }
        a[i] = c[i] + d[i] * e[i];
        goto L10;
L20:
        b[i] = a[i] + d[i] * d[i];
L10:
        ;
    }
}


/*after removing goto:
TYPE s1161(int count)
{
    for (int i = 0; i < count*8-1; ++i) {
        if (c[i] < (float)0.) {
            b[i] = a[i] + d[i] * d[i];
        }
        else {
            a[i] = c[i] + d[i] * e[i];
        }
    }
}*/

int nondet();

int main() {
	int count = nondet();
	s1161(count);
}