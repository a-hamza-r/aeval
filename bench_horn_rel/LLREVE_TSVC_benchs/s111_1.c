#include "declarations.h"

//	linear dependence testing
//	no dependence - vectorizable

int s111(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 1; i < count*8; i+=2) {
    a[i] = a[i-1] + b[i];
  }
  return 0;
}
