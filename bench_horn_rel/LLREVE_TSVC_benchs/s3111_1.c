#include "declarations.h"

//    reductions
//    conditional sum reduction

TYPE s3111(int count) {
if (count <= 0 || count > 10) return 1;
  TYPE sum = 0;
  for (int i = 0; i < count*8; i++) {
      if (a[i] > 0) {
          sum += a[i];
      }
  }
  return sum;
}

