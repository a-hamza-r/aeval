#include "declarations.h"

//  symbolics
//  expression in loop bounds and subscripts

int s173(int count) {
if (count <= 0 || count > 10) return 1;
  int k = count*4;
  for (int i = 0; i < k; i+=4) {
    a[i+k] = a[i] + b[i];
    a[i+1+k] = a[i+1] + b[i+1];
    a[i+2+k] = a[i+2] + b[i+2];
    a[i+3+k] = a[i+3] + b[i+3];
  }
  return 0;
}

