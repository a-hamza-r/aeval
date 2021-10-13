#include "declarations.h"

//	induction variables
//	coupled induction variables
//	jump in data access

int s128(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*4; i++) {
		a[i] = b[2*i] - d[i];
		b[2*i] = a[i] + c[2*i];
	}
  return 0;
}

