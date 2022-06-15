#include "declarations.h"

//	scalar and array expansion
//	wrap-around scalar under an if

int s261(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 1; i < count*8; ++i) {
		e[i] = a[i] + b[i];
		a[i] = e[i] + c[i-1];
		e[i] = c[i] * d[i];
		c[i] = e[i];
	}
	return 0;
}

