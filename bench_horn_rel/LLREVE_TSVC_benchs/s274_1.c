#include "declarations.h"

//	control flow
//	complex loop with dependent conditional

int s274(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8; i++) {
		a[i] = c[i] + e[i] * d[i];
		if (a[i] > 0) {
			b[i] = a[i] + b[i];
		} else {
			a[i] = d[i] * e[i];
		}
	}
	return 0;
}

