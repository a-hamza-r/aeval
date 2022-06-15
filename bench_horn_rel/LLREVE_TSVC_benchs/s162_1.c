#include "declarations.h"

//	control flow
//	deriving assertions

int s162(int count, int k) {
if (count <= 0 || count > 10) return 1;
  if (k > 0) {
    for (int i = 0; i < count*8-1; i++) {
      a[i] = a[i + k] + b[i] * c[i];
    }
  }
  return 0;
}

