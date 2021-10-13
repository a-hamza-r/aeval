#include "declarations.h"

//    parameters
//    parameter statement

int s431(int count) {
if (count <= 0 || count > 10) return 1;
  int k=0;
  for (int i = 0; i < count*8; i+=8) {
    a[i] = a[i+k] + b[i];
    a[i+1] = a[i+1+k] + b[i+1];
    a[i+2] = a[i+2+k] + b[i+2];
    a[i+3] = a[i+3+k] + b[i+3];
    a[i+4] = a[i+4+k] + b[i+4];
    a[i+5] = a[i+5+k] + b[i+5];
    a[i+6] = a[i+6+k] + b[i+6];
    a[i+7] = a[i+7+k] + b[i+7];
  }
  return 0;
}

