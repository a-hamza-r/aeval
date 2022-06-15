#include "declarations.h"

//    control flow
//    tests for recognition of loop independent dependences
//    between statements in mutually exclusive regions.

int s1161(int count)
{
if (count <= 0 || count > 10) return 1;
    for (int i = 0; i < count*8-1; ++i) {
        if (c[i] < 0) {
            b[i] = a[i] + d[i] * d[i];
        }
        else {
            a[i] = c[i] + d[i] * e[i];
        }
    }
    return 0;
}