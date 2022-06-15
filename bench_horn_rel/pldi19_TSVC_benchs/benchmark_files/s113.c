#include "declarations.h"

//	linear dependence testing
//	a(i)=a(1) but no actual dependence cycle

TYPE 
__attribute__((noinline))
s113(TYPE* a, TYPE* b, int count) {
	for (int i = 1; i < count*8; i++) {
		a[i] = a[0] + b[i];
	}
	return 0;
}

TYPE 
__attribute__((noinline))
s113_vec(TYPE* a, TYPE* b, int count) {
	if (count > 0) {
	a[1] = a[0] + b[1];
	a[1+1] = a[0] + b[1+1];
	a[1+2] = a[0] + b[1+2];
	a[1+3] = a[0] + b[1+3];
	a[1+4] = a[0] + b[1+4];
	a[1+5] = a[0] + b[1+5];
	a[1+6] = a[0] + b[1+6];
}
	for (int i = 8; i < count*8; i+=8) {
		a[i] = a[0] + b[i];
		a[i+1] = a[0] + b[i+1];
		a[i+2] = a[0] + b[i+2];
		a[i+3] = a[0] + b[i+3];
		a[i+4] = a[0] + b[i+4];
		a[i+5] = a[0] + b[i+5];
		a[i+6] = a[0] + b[i+6];
		a[i+7] = a[0] + b[i+7];
	}
	return 0;
}


int main() {
	return 0;
}