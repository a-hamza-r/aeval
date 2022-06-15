#include "declarations.h"

//	symbolics
//	expression in loop bounds and subscripts

int s173(int count) {
if (count <= 0 || count > 10) return 1;
  int k = count*4;
  for (int i = 0; i < k; i++) {
    a[i+k] = a[i] + b[i];
  }
  return 0;
}

