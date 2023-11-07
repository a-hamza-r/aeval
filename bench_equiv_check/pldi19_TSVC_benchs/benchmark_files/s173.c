#include "declarations.h"

//	symbolics
//	expression in loop bounds and subscripts

TYPE 
__attribute__((noinline))
s173(TYPE* a, TYPE* b, int count) {
  int k = count*4;
  for (int i = 0; i < k; i++) {
    a[i+k] = a[i] + b[i];
  }
  return 0;
}

TYPE 
__attribute__((noinline))
s173_vec(TYPE* a, TYPE* b, int count) {
  int k = count*4;
  for (int i = 0; i < k; i+=8) {
    a[i+k] = a[i] + b[i];
    a[i+1+k] = a[i+1] + b[i+1];
    a[i+2+k] = a[i+2] + b[i+2];
    a[i+3+k] = a[i+3] + b[i+3];
  }
  return 0;
}

int main() {
	return 0;
}