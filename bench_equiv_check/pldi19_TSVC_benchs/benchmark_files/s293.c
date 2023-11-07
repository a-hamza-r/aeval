#include "declarations.h"

//	loop peeling
//	a(i)=a(0) with actual dependence cycle, loop is vectorizable

TYPE 
__attribute__((noinline))
s293(TYPE* a, int count) {
	for (int i = 0; i < count*8; i++) {
		a[i] = a[0];
	}
  return 0;
}

TYPE 
__attribute__((noinline))
s293_vec(TYPE* a, int count) {
	for (int i = 0; i < count*8; i+=8) {
		a[i] = a[0];
		a[i+1] = a[0];
		a[i+2] = a[0];
		a[i+3] = a[0];
		a[i+4] = a[0];
		a[i+5] = a[0];
		a[i+6] = a[0];
		a[i+7] = a[0];
	}
  return 0;
}

int main() {
	return 0;
}