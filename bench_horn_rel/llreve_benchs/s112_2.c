#include "declarations.h"

//	linear dependence testing
//	loop reversal

int s112(int count) {
if (count <= 0 || count > 10) return 1;
  a[count*8-1] = a[count*8-1-1] + b[count*8-1];
  a[count*8-2] = a[count*8-2-1] + b[count*8-2];
  a[count*8-3] = a[count*8-3-1] + b[count*8-3];
  a[count*8-4] = a[count*8-4-1] + b[count*8-4];
  a[count*8-5] = a[count*8-5-1] + b[count*8-5];
  a[count*8-6] = a[count*8-6-1] + b[count*8-6];
  a[count*8-7] = a[count*8-7-1] + b[count*8-7];
  for (int i = count*8-8; i >= 1; i-=8) {
    a[i] = a[i-1] + b[i];
    a[i-1] = a[i-1-1] + b[i-1];
    a[i-2] = a[i-2-1] + b[i-2];
    a[i-3] = a[i-3-1] + b[i-3];
    a[i-4] = a[i-4-1] + b[i-4];
    a[i-5] = a[i-5-1] + b[i-5];
    a[i-6] = a[i-6-1] + b[i-6];
    a[i-7] = a[i-7-1] + b[i-7];
  }
  return 0;
}

