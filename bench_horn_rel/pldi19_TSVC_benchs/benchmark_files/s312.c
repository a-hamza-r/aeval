#include "declarations.h"

TYPE 
__attribute__((noinline))
s312(TYPE* a, int count) {
	TYPE prod = 1;
	for (int i = 0; i < count*8; i++) {
		prod *= a[i];
	}
	return prod;
}

TYPE 
__attribute__((noinline))
s312_vec(TYPE* a, int count) {
	TYPE prod = 1;
	for (int i = 0; i < count*8; i+=8) {
		prod *= a[i];
		prod *= a[i+1];
		prod *= a[i+2];
		prod *= a[i+3];
		prod *= a[i+4];
		prod *= a[i+5];
		prod *= a[i+6];
		prod *= a[i+7];
	}
	return prod;
}

int main() {
	return 0;
}