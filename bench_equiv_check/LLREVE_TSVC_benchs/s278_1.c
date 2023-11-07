#include "declarations.h"

//	control flow
//	if/goto to block if-then-else

int s278(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8; i++) {
		if (a[i] > 0) {
			c[i] = -c[i] + d[i] * e[i];
		}
		else {
			b[i] = -b[i] + d[i] * e[i];
		}
		a[i] = b[i] + c[i] * d[i];
	}
	return 0;
}

