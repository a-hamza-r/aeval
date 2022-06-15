#include "declarations.h"

//	control loops
//	vector dot product reduction

TYPE vdotr(int count) {
if (count <= 0 || count > 10) return 1;
  TYPE sum = 0;
  for (int i = 0; i < count*8; i++) {
    sum += a[i]*b[i];
  }
  return sum;
}

