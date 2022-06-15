#include "declarations.h"

//	symbolics
//	convolution

/** vectorizes with gcc */
TYPE 
__attribute__((noinline))
S176(TYPE* a, TYPE *b, TYPE *c, int count) {
  int m = count*4;
  for (int j = 0; j < m; j++) {
    for (int i = 0; i < m; i++) {
      a[i] += b[i+m-j-1] * c[j];
    }
  }
  return 0;
}

TYPE 
__attribute__((noinline))
s176_vec(TYPE* a, TYPE *b, TYPE *c, int count) {
  int m = count*4;
  for (int j = 0; j < m; j++) {
    for (int i = 0; i < m; i+=4) {
      a[i] += b[i+m-j-1] * c[j];
      a[i+1] += b[i+1+m-j-1] * c[j];
      a[i+2] += b[i+2+m-j-1] * c[j];
      a[i+3] += b[i+3+m-j-1] * c[j];
    }
  }
  return 0;
}

int main() {
	return 0;
}