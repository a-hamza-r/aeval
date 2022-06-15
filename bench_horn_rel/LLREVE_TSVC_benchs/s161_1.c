#include "declarations.h"

//	control flow
//	tests for recognition of loop independent dependences
//	between statements in mutually exclusive regions.

int s161(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8-1; ++i) {
		if (b[i] < 0) {
			c[i+1] = a[i] + d[i] * d[i];
		}
		else {
			a[i] = c[i] + d[i] * e[i];
		}
	}
  return 0;
}
