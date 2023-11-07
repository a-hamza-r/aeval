#include "declarations.h"

//	crossing thresholds
//	index set splitting
//	reverse data access

int s281(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8; i++) {
		e[i] = a[count*8-i-1] + b[i] * c[i];
		a[i] = e[i]-1;
		b[i] = e[i];
	}
  return 0;
}

