#include "declarations.h"


TYPE sum1d(int count) {
if (count <= 0 || count > 10) return 1;
  TYPE sum = 0;
  for (int i = 0; i < count*8; i+=8) {
    sum += a[i];
    sum += a[i+1];
    sum += a[i+2];
    sum += a[i+3];
    sum += a[i+4];
    sum += a[i+5];
    sum += a[i+6];
    sum += a[i+7];
  }
  return sum;
}

