#include "declarations.h"

TYPE 
__attribute__((noinline))
motivating_example(TYPE* a, TYPE* b, int count) {
  for (int i = 0; i < count*4-1; i++) {
		a[i] = a[i+1] + b[i];
  }
  return 0;
}

TYPE 
__attribute__((noinline))
motivating_example_vec(TYPE* a, TYPE* b, int count) {
  if (count > 0) {
  a[0] = a[0+1] + b[0];
  a[1] = a[1+1] + b[1];
}
  for (int i = 2; i < count*4-2; i+=4) {
    a[i] = a[i+1] + b[i];
    a[i+1] = a[i+1+1] + b[i+1];
    a[i+2] = a[i+2+1] + b[i+2];
    a[i+3] = a[i+3+1] + b[i+3];
  }
  if (count > 0)
  a[count*4-2] = a[count*4-1] + b[count*4-2];
  return 0;
}

int main() {
  return 0;
}
