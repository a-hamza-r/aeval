#include "declarations.h"

//	control flow
//	test for dependences arising from guard variable computation.

int s277(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8-1; i++) {
		if (b[i] >= 0) {
			b[i+1] = c[i] + d[i] * e[i];
		}
	}
	return 0;
}

