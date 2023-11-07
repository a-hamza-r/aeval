#include "declarations.h"

//	no dependence - vectorizable
//	jump in data access

TYPE 
__attribute__((noinline))
s1111(TYPE* a, TYPE* b, TYPE *c, TYPE *d, TYPE *e, int count) {
  for (int i = 0; i < count*4; i++) {
	  a[2*i] = c[i] * b[i] + d[i] * b[i] + c[i] * c[i] + d[i] * b[i] + d[i] * c[i];
  }
  return 0;
}

TYPE 
__attribute__((noinline))
s1111_vec(TYPE* a, TYPE* b, TYPE *c, TYPE *d, TYPE *e, int count) {
  for (int i = 0; i < count*4; i+=4) {
    a[2*i] = c[i] * b[i] + d[i] * b[i] + c[i] * c[i] + d[i] * b[i] + d[i] * c[i];
    a[2*(i+1)] = c[(i+1)] * b[(i+1)] + d[(i+1)] * b[(i+1)] + c[(i+1)] * c[(i+1)] + d[(i+1)] * b[(i+1)] + d[(i+1)] * c[(i+1)];
    a[2*(i+2)] = c[(i+2)] * b[(i+2)] + d[(i+2)] * b[(i+2)] + c[(i+2)] * c[(i+2)] + d[(i+2)] * b[(i+2)] + d[(i+2)] * c[(i+2)];
    a[2*(i+3)] = c[(i+3)] * b[(i+3)] + d[(i+3)] * b[(i+3)] + c[(i+3)] * c[(i+3)] + d[(i+3)] * b[(i+3)] + d[(i+3)] * c[(i+3)];
  }
  return 0;
}


int main() {
	return 0;
}