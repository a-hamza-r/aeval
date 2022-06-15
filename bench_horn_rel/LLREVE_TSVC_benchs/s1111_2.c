#include "declarations.h"

//	no dependence - vectorizable
//	jump in data access

int s1111(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 0; i < count*4; i+=4) {
	  a[2*i] = c[i] * b[i] + d[i] * b[i] + c[i] * c[i] + d[i] * b[i] + d[i] * c[i];
	  a[2*(i+1)] = c[(i+1)] * b[(i+1)] + d[(i+1)] * b[(i+1)] + c[(i+1)] * c[(i+1)] + d[(i+1)] * b[(i+1)] + d[(i+1)] * c[(i+1)];
	  a[2*(i+2)] = c[(i+2)] * b[(i+2)] + d[(i+2)] * b[(i+2)] + c[(i+2)] * c[(i+2)] + d[(i+2)] * b[(i+2)] + d[(i+2)] * c[(i+2)];
	  a[2*(i+3)] = c[(i+3)] * b[(i+3)] + d[(i+3)] * b[(i+3)] + c[(i+3)] * c[(i+3)] + d[(i+3)] * b[(i+3)] + d[(i+3)] * c[(i+3)];
  }
  return 0;
}
