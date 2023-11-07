#include "declarations.h"

//	control loops
//	vector plus vector

TYPE 
__attribute__((noinline))
vpv(TYPE* a, TYPE* b, int count) {
  for (int i = 0; i < count*8; i++) {
    a[i] += b[i];
  }
  return 0;
}

TYPE 
__attribute__((noinline))
vpv_vec(TYPE* a, TYPE* b, int count) {
  for (int i = 0; i < count*8; i+=8) {
    a[i] += b[i];
    a[i+1] += b[i+1];
    a[i+2] += b[i+2];
    a[i+3] += b[i+3];
    a[i+4] += b[i+4];
    a[i+5] += b[i+5];
    a[i+6] += b[i+6];
    a[i+7] += b[i+7];
  }
  return 0;
}


int main() {
  return 0;
}