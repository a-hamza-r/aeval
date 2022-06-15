#include "declarations.h"

//	linear dependence testing
//	loop reversal

int s1112(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = count*8-1; i >= 0; i-=8) {
    a[i] = b[i] + 1;
    a[(i-1)] = b[(i-1)] + 1;
    a[(i-2)] = b[(i-2)] + 1;
    a[(i-3)] = b[(i-3)] + 1;
    a[(i-4)] = b[(i-4)] + 1;
    a[(i-5)] = b[(i-5)] + 1;
    a[(i-6)] = b[(i-6)] + 1;
    a[(i-7)] = b[(i-7)] + 1;
  }
  return 0;
}
