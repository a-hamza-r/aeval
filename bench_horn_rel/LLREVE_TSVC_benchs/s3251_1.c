#include "declarations.h"

//	scalar and array expansion
//	scalar expansion

int s3251(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 0; i < count*8-1; i++) {
		a[i+1] = b[i]+c[i];
		b[i]   = c[i]*e[i];
		d[i]   = a[i]*e[i];
  }
  return 0;
}

