#include "declarations.h"

//	node splitting
//	preloading necessary to allow vectorization

int s241(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8-1; i++) {
		e[i] = a[i+1];
		a[i] = b[i] * c[i  ] * d[i];
		b[i] = a[i] * e[i] * d[i];
	}
	return 0;
}

