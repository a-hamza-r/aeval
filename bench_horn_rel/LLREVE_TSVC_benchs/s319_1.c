#include "declarations.h"


TYPE s319(int count) {
if (count <= 0 || count > 10) return 1;
  TYPE sum = 0;
  for (int i = 0; i < count*8; i++) {
      a[i] = c[i] + d[i];
      sum += a[i];
      b[i] = c[i] + e[i];
      sum += b[i];
  }
  return sum;
}

