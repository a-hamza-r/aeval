#include "declarations.h"

//	linear dependence testing
//	loop reversal

int s112(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = count*8-1; i >= 1; i--) {
    a[i] = a[i-1] + b[i];
  }
  return 0;
}

