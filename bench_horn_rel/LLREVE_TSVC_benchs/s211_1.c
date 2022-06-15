#include "declarations.h"

//	statement reordering
//	statement reordering allows vectorization

int s211(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 1; i < count*8-1; i++) {
		b[i] = b[i + 1] - e[i] * d[i];
		a[i] = b[i - 1] + c[i] * d[i];
	}
	return 0;
}

