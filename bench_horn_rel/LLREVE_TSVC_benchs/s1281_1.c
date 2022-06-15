#include "declarations.h"

//	crossing thresholds
//	index set splitting
//	reverse data access

int s1281(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8; i++) {
		f[i] = b[i]*c[i]+a[i]*d[i]+e[i];
		a[i] = f[i]-1;
		b[i] = f[i];
	}
  return 0;
}

