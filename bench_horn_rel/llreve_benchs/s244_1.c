#include "declarations.h"

//	node splitting
//	false dependence cycle breaking

int s244(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8-1; ++i) {
		a[i+1] = c[i] + b[i] + a[i+1] * d[i];
		a[i] = b[i] + c[i] * d[i];
		b[i] = c[i] + b[i];
	}
  return 0;
}

