#include "declarations.h"

int s000(int count) {
if (count <= 0 || count > 10) return 1;
  int i = 0;
  while ( i < count*8) {
    a[i] = b[i] + 1;
    a[i+1] = b[i+1] + 1;
    a[i+2] = b[i+2] + 1;
    a[i+3] = b[i+3] + 1;
    a[i+4] = b[i+4] + 1;
    a[i+5] = b[i+5] + 1;
    a[i+6] = b[i+6] + 1;
    a[i+7] = b[i+7] + 1;
    i+=8;
  }
  return 0;
}
