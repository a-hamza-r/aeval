#include "declarations.h"

//	control flow
//	if test using loop index

int s276(int count, int mid) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8; i++) {
		if (i+1 < mid) {
			a[i] += b[i] * c[i];
		} else {
			a[i] += b[i] * d[i];
		}
	}
	return 0;
}

