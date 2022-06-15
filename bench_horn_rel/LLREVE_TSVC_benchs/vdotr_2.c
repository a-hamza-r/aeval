#include "declarations.h"

//  control loops
//  vector dot product reduction

TYPE vdotr(int count) {
if (count <= 0 || count > 10) return 1;
  TYPE sum = 0;
  for (int i = 0; i < count*8; i+=8) {
    sum += a[i]*b[i];
    sum += a[i+1]*b[i+1];
    sum += a[i+2]*b[i+2];
    sum += a[i+3]*b[i+3];
    sum += a[i+4]*b[i+4];
    sum += a[i+5]*b[i+5];
    sum += a[i+6]*b[i+6];
    sum += a[i+7]*b[i+7];
  }
  return sum;
}

