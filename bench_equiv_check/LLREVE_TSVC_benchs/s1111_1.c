#include "declarations.h"

//	no dependence - vectorizable
//	jump in data access

int s1111(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 0; i < count*4; i++) {
	  a[2*i] = c[i] * b[i] + d[i] * b[i] + c[i] * c[i] + d[i] * b[i] + d[i] * c[i];
  }
  return 0;
}
