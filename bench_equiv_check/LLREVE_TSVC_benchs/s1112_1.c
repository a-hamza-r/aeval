#include "declarations.h"

//	linear dependence testing
//	loop reversal

int s1112(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = count*8-1; i >= 0; i--) {
    a[i] = b[i] + 1;
  }
  return 0;
}
