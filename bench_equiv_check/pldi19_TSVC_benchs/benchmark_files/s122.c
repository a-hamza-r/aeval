#include "declarations.h"

//	induction variable recognition
//	variable lower and upper bound, and stride
//	reverse data access and jump in data access

TYPE 
__attribute__((noinline))
s122(TYPE* a, TYPE* b, int count) {
  // int k = 0;
  for (int i = 1; i < count*8; i++) {
    // k++;
    // a[i] += b[count*8-k];
    a[i] += b[count*8-i];
  }
  return 0;
}

TYPE 
__attribute__((noinline))
s122_vec(TYPE* a, TYPE* b, int count) {
  // int k = 0;
  if (count > 0) {
  a[1] += b[count*8-1];
  a[2] += b[count*8-2];
  a[3] += b[count*8-3];
  a[4] += b[count*8-4];
  a[5] += b[count*8-5];
  a[6] += b[count*8-6];
  a[7] += b[count*8-7];
}
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

int main() {
	return 0;
}