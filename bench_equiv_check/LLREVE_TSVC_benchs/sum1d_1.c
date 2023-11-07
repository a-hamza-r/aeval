#include "declarations.h"


TYPE sum1d(int count) {
if (count <= 0 || count > 10) return 1;
  TYPE sum = 0;
  for (int i = 0; i < count*8; i++) {
    sum += a[i];
  }
  return sum;
}

