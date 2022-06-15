#include "declarations.h"

//	linear dependence testing
//	no dependence - vectorizable

TYPE 
__attribute__((noinline))
s1119(TYPE** aa, TYPE** bb, int count) {
	for (int i = 1; i < count*8; i++) {
		for (int j = 0; j < count*8; j++) {
			aa[i][j] = aa[i-1][j] + bb[i][j];
		}
	}
	return 0;
}

TYPE 
__attribute__((noinline))
s1119_vec(TYPE** aa, TYPE** bb, int count) {
	for (int i = 1; i < count*8; i++) {
		for (int j = 0; j < count*8; j+=8) {
			aa[i][j] = aa[i-1][j] + bb[i][j];
			aa[i][j+1] = aa[i-1][j+1] + bb[i][j+1];
			aa[i][j+2] = aa[i-1][j+2] + bb[i][j+2];
			aa[i][j+3] = aa[i-1][j+3] + bb[i][j+3];
			aa[i][j+4] = aa[i-1][j+4] + bb[i][j+4];
			aa[i][j+5] = aa[i-1][j+5] + bb[i][j+5];
			aa[i][j+6] = aa[i-1][j+6] + bb[i][j+6];
			aa[i][j+7] = aa[i-1][j+7] + bb[i][j+7];
		}
	}
	return 0;
}

int main() {
	return 0;
}