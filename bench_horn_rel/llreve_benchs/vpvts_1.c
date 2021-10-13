#include "declarations.h"

//	control loops
//	vector plus vector times scalar

int vpvts(int count, TYPE k) {
if (count <= 0 || count > 10) return 1;
  for (int i = 0; i < count*8; i++) {
    a[i] += b[i]*k;
  }
  return 0;
}

