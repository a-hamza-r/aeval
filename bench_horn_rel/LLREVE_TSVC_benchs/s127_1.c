#include "declarations.h"

//  induction variable recognition
//  induction variable with multiple increments

int s127(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 0; i < count*4-1; i++) {
    a[2*i] = b[i] + c[i] * d[i];
    a[2*i+1] = b[i] + d[i] * e[i];
  }
  return 0;
}
