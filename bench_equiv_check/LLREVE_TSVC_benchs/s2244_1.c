#include "declarations.h"

//	node splitting
//	cycle with true and anti dependency

int s2244(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8-1; i++) {
		a[i+1] = b[i] + e[i];
		a[i] = b[i] + c[i];
	}
  return 0;
}

