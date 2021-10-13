#include "declarations.h"

//	induction variables
//	coupled induction variables
//	jump in data access

int s128(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*4; i+=4) {
		a[i] = b[2*i] - d[i];
		b[2*i] = a[i] + c[2*i];

		a[(i+1)] = b[2*(i+1)] - d[(i+1)];
		b[2*(i+1)] = a[(i+1)] + c[2*(i+1)];

		a[(i+2)] = b[2*(i+2)] - d[(i+2)];
		b[2*(i+2)] = a[(i+2)] + c[2*(i+2)];

		a[(i+3)] = b[2*(i+3)] - d[(i+3)];
		b[2*(i+3)] = a[(i+3)] + c[2*(i+3)];
	}
  return 0;
}

