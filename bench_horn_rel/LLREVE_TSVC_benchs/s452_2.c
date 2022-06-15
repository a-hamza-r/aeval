#include "declarations.h"

//  intrinsic functions
//  seq function

int s452(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 0; i < count*8; i+=8) {
    a[i] = b[i] + c[i] * (i+1);
    a[i+1] = b[i+1] + c[i+1] * (i+1+1);
    a[i+2] = b[i+2] + c[i+2] * (i+2+1);
    a[i+3] = b[i+3] + c[i+3] * (i+3+1);
    a[i+4] = b[i+4] + c[i+4] * (i+4+1);
    a[i+5] = b[i+5] + c[i+5] * (i+5+1);
    a[i+6] = b[i+6] + c[i+6] * (i+6+1);
    a[i+7] = b[i+7] + c[i+7] * (i+7+1);
  }
  return 0;
}

