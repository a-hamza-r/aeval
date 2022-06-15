#include "declarations.h"

//	linear dependence testing
//	one iteration dependency on a(count*4) but still vectorizable

int s1113(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8; i++) {
		a[i] = a[count*4] + b[i];
	}
  return 0;
}

