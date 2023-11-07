#include "declarations.h"

//	run-time symbolic resolution

TYPE 
__attribute__((noinline))
s1221(TYPE* a, TYPE* b, int count) {
  for (int i = 4; i < count*8; i++) {
    a[i] = a[i-4] + b[i];
  }
  return 0;
}

TYPE 
__attribute__((noinline))
s1221_vec(TYPE* a, TYPE* b, int count) {
  for (int i = 4; i < count*8; i+=4) {
    a[i] = a[i-4] + b[i];
    a[i+1] = a[i-3] + b[i+1];
    a[i+2] = a[i-2] + b[i+2];
    a[i+3] = a[i-1] + b[i+3];
  }
  return 0;
}

int main() {
  return 0;
}