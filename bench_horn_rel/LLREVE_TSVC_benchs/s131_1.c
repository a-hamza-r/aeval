#include "declarations.h"

//	global data flow analysis
//	forward substitution

int s131(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8 - 1; i++) {
		a[i] = a[i + 1] + b[i];
	}
	return 0;
}

