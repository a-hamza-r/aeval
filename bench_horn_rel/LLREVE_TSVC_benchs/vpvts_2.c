#include "declarations.h"

//	control loops
//	vector plus vector times scalar

int vpvts(int count, TYPE k) {
if (count <= 0 || count > 10) return 1;
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
