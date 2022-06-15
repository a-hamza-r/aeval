#include "declarations.h"

//	diagonals
//	identity matrix, best results vectorize both inner and outer loops

TYPE 
__attribute__((noinline))
s2102(TYPE** aa, int count) {
	for (int j = 0; j < count*8; j++) {
		for (int i = 0; i < count*8; i++) {
			aa[j][i] = 0;
		}
		aa[j][j] = 1;
	}
  return 0;
}

TYPE 
__attribute__((noinline))
s2102_vec(TYPE** aa, int count) {
	for (int j = 0; j < count*8; j++) {
		for (int i = 0; i < count*8; i+=8) {
			aa[j][i] = 0;
			aa[j][i+1] = 0;
			aa[j][i+2] = 0;
			aa[j][i+3] = 0;
			aa[j][i+4] = 0;
			aa[j][i+5] = 0;
			aa[j][i+6] = 0;
			aa[j][i+7] = 0;
		}
		aa[j][j] = 1;
	}
  return 0;
}

int main() {
	return 0;
}