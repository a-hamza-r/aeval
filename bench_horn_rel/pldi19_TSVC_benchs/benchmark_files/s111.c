#include "declarations.h"

//	linear dependence testing
//	no dependence - vectorizable

TYPE 
__attribute__((noinline))
s111(TYPE* a, TYPE* b, int count) {
  for (int i = 1; i < count*8; i+=2) {
    a[i] = a[i-1] + b[i];
  }
  return 0;
}

TYPE 
__attribute__((noinline))
s111_vec(TYPE* a, TYPE* b, int count) {
  for (int i = 1; i < count*8; i+=8) {
    a[i] = a[i-1] + b[i];
    a[(i+2)] = a[(i+2)-1] + b[(i+2)];
    a[(i+4)] = a[(i+4)-1] + b[(i+4)];
    a[(i+6)] = a[(i+6)-1] + b[(i+6)];
  }
  return 0;
}


int main() {
	return 0;
}