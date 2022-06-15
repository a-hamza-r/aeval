#include "declarations.h"

//	control flow
//	simple loop with dependent conditional

int s273(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8; i++) {
		a[i] += d[i] * e[i];
		if (a[i] < 0)
			b[i] += d[i] * e[i];
		c[i] += a[i] * d[i];
	}
	return 0;
}

