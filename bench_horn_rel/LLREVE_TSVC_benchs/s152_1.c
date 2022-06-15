#include "declarations.h"

//	control loops
//	vector dot product reduction

int s152(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8; i++) {
		b[i] = d[i] * e[i];
		a[i] += b[i] * c[i];
	}
  return 0;
}
