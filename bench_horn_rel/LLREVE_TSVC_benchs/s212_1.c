#include "declarations.h"

//	statement reordering
//	dependency needing temporary

int s212(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8-1; i++) {
		b[i] += a[i + 1] * d[i];
		a[i] *= c[i];
	}
  return 0;
}

