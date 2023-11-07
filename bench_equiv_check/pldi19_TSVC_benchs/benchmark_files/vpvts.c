#include "declarations.h"

//	control loops
//	vector plus vector times scalar

TYPE 
__attribute__((noinline))
vpvts(TYPE* a, TYPE* b, int count, TYPE k) {
  for (int i = 0; i < count*8; i++) {
    a[i] += b[i]*k;
  }
  return 0;
}

TYPE 
__attribute__((noinline))
vpvts_vec(TYPE* a, TYPE* b, int count, TYPE k) {
  for (int i = 0; i < count*8; i+=8) {
    a[i] += b[i]*k;
    a[i+1] += b[i+1]*k;
    a[i+2] += b[i+2]*k;
    a[i+3] += b[i+3]*k;
    a[i+4] += b[i+4]*k;
    a[i+5] += b[i+5]*k;
    a[i+6] += b[i+6]*k;
    a[i+7] += b[i+7]*k;
  }
  return 0;
}


int main() {
  return 0;
}