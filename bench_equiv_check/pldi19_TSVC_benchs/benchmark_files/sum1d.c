#include "declarations.h"

TYPE 
__attribute__((noinline))
sum1d(TYPE* a, int count) {
  TYPE sum = 0;
  for (int i = 0; i < count*8; i++) {
    sum += a[i];
  }
  return sum;
}

TYPE 
__attribute__((noinline))
sum1d_vec(TYPE* a, int count) {
  TYPE sum = 0;
  for (int i = 0; i < count*8; i+=8) {
    sum += a[i];
    sum += a[i+1];
    sum += a[i+2];
    sum += a[i+3];
    sum += a[i+4];
    sum += a[i+5];
    sum += a[i+6];
    sum += a[i+7];
  }
  return sum;
}


int main() {
	return 0;
}