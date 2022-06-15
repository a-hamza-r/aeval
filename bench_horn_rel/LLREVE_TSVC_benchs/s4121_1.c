#include "declarations.h"

//    statement functions
//    elementwise multiplication

int s4121(int count) {
if (count <= 0 || count > 10) return 1;
    for (int i = 0; i < count*8; i++) {
        a[i] += b[i]*c[i];
    }
    return 0;
}

