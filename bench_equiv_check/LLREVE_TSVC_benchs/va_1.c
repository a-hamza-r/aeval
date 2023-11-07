#include "declarations.h"

//    control loops
//    vector assignment

int va(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 0; i < count*8; i++) {
    a[i] = b[i];
  }
  return 0;
}

