#include "declarations.h"

//    control loops
//    vector assignment, gather
//    gather is required

TYPE 
__attribute__((noinline))
vag(TYPE* a, TYPE *b, int *ip, int count) {
  for (int i = 0; i < count*8; i++) {
    a[i] = b[ip[i]];
  }
  return 0;
}

TYPE 
__attribute__((noinline))
vag_vec(TYPE* a, TYPE *b, int *ip, int count) {
  for (int i = 0; i < count*8; i+=8) {
    a[i] = b[ip[i]];
    a[i+1] = b[ip[i+1]];
    a[i+2] = b[ip[i+2]];
    a[i+3] = b[ip[i+3]];
    a[i+4] = b[ip[i+4]];
    a[i+5] = b[ip[i+5]];
    a[i+6] = b[ip[i+6]];
    a[i+7] = b[ip[i+7]];
  }
  return 0;
}

int main() {
	return 0;
}