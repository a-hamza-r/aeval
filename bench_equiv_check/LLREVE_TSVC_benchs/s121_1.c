#include "declarations.h"

//	induction variable recognition
//	loop with possible ambiguity because of scalar store

int s121(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 0; i < count*8-1; i++) {
    a[i] = a[i+1] + b[i];
  }
  return 0;
}
