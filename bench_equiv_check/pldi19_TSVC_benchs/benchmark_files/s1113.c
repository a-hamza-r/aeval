#include "declarations.h"

//	linear dependence testing
//	one iteration dependency on a(count*4) but still vectorizable

TYPE 
__attribute__((noinline))
s1113(TYPE* a, TYPE* b, int count) {
	for (int i = 0; i < count*8; i++) {
		a[i] = a[count*4] + b[i];
	}
  return 0;
}

TYPE 
__attribute__((noinline))
s1113_vec(TYPE* a, TYPE* b, int count) {
	for (int i = 0; i < count*8; i+=8) {
		a[i] = a[count*4] + b[i];
		a[i+1] = a[count*4] + b[i+1];
		a[i+2] = a[count*4] + b[i+2];
		a[i+3] = a[count*4] + b[i+3];
		a[i+4] = a[count*4] + b[i+4];
		a[i+5] = a[count*4] + b[i+5];
		a[i+6] = a[count*4] + b[i+6];
		a[i+7] = a[count*4] + b[i+7];
	}
  return 0;
}

int main() {
	return 0;
}