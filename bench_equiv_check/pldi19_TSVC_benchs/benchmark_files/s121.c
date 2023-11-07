#include "declarations.h"

//	induction variable recognition
//	loop with possible ambiguity because of scalar store

TYPE 
__attribute__((noinline))
s121(TYPE* a, TYPE* b, int count) {
  for (int i = 0; i < count*8-1; i++) {
    a[i] = a[i+1] + b[i];
  }
  return 0;
}

TYPE 
__attribute__((noinline))
s121_vec(TYPE* a, TYPE* b, int count) {
  if (count > 0) {
  a[0] = a[1] + b[0];
  a[1] = a[2] + b[1];
  a[2] = a[3] + b[2];
  a[3] = a[4] + b[3];
  a[4] = a[5] + b[4];
  a[5] = a[6] + b[5];
  a[6] = a[7] + b[6];
}
  for (int i = 7; i < count*8-1; i+=8) {
    a[i] = a[i+1] + b[i];
    a[i+1] = a[i+2] + b[i+1];
    a[i+2] = a[i+3] + b[i+2];
    a[i+3] = a[i+4] + b[i+3];
    a[i+4] = a[i+5] + b[i+4];
    a[i+5] = a[i+6] + b[i+5];
    a[i+6] = a[i+7] + b[i+6];
    a[i+7] = a[i+8] + b[i+7];
  }
  return 0;
}

int main() {
	return 0;
}