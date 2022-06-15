#include "declarations.h"

//	scalar and array expansion
//	scalar expansion assigned under if

int s253(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8; i++) {
		if (a[i] > b[i]) {
			s[i] = a[i] - b[i] * d[i];
			c[i] += s[i];
			a[i] = s[i];
		}
	}
  return 0;
}

