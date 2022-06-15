#include "declarations.h"

//	induction variable recognition
//	variable lower and upper bound, and stride
//	reverse data access and jump in data access

int s122(int count) {
if (count <= 0 || count > 10) return 1;
  // int k = 0;
  for (int i = 1; i < count*8; i++) {
    a[i] += b[count*8-i];
  }
  return 0;
}
