#include "declarations.h"

//	induction variable recognition
//	variable lower and upper bound, and stride
//	reverse data access and jump in data access

int s122(int count) {
if (count <= 0 || count > 10) return 1;
  // int k = 0;
  a[1] += b[count*8-1];
  a[(1+1)] += b[count*8-(1+1)];
  a[(1+2)] += b[count*8-(1+2)];
  a[(1+3)] += b[count*8-(1+3)];
  a[(1+4)] += b[count*8-(1+4)];
  a[(1+5)] += b[count*8-(1+5)];
  a[(1+6)] += b[count*8-(1+6)];
  for (int i = 8; i < count*8; i+=8) {
    a[i] += b[count*8-i];
    a[(i+1)] += b[count*8-(i+1)];
    a[(i+2)] += b[count*8-(i+2)];
    a[(i+3)] += b[count*8-(i+3)];
    a[(i+4)] += b[count*8-(i+4)];
    a[(i+5)] += b[count*8-(i+5)];
    a[(i+6)] += b[count*8-(i+6)];
    a[(i+7)] += b[count*8-(i+7)];
  }
  return 0;
}

