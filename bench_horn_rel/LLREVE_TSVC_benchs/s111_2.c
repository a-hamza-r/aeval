#include "declarations.h"

//	linear dependence testing
//	no dependence - vectorizable

int s111(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 1; i < count*8; i+=8) {
    a[i] = a[i-1] + b[i];
    a[i+2] = a[i+2-1] + b[i+2];
    a[i+4] = a[i+4-1] + b[i+4];
    a[i+6] = a[i+6-1] + b[i+6];
  }
  return 0;
}
