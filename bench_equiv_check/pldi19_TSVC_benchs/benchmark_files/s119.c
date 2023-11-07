#include "declarations.h"

//	linear dependence testing
//	no dependence - vectorizable

TYPE 
__attribute__((noinline))
s119(TYPE** aa, TYPE** bb, int count) {
	for (int i = 1; i < count*8; i++) {
		for (int j = 1; j < count*8; j++) {
			aa[i][j] = aa[i-1][j-1] + bb[i][j];
		}
	}
	return 0;
}

TYPE 
__attribute__((noinline))
s119_vec(TYPE** aa, TYPE** bb, int count) {
	for (int i = 1; i < count*8; i++) {
		if (count > 0) {
		aa[i][1] = aa[i-1][1-1] + bb[i][1];
		aa[i][1+1] = aa[i-1][1+1-1] + bb[i][1+1];
		aa[i][1+2] = aa[i-1][1+2-1] + bb[i][1+2];
		aa[i][1+3] = aa[i-1][1+3-1] + bb[i][1+3];
		aa[i][1+4] = aa[i-1][1+4-1] + bb[i][1+4];
		aa[i][1+5] = aa[i-1][1+5-1] + bb[i][1+5];
		aa[i][1+6] = aa[i-1][1+6-1] + bb[i][1+6];
	}
		for (int j = 8; j < count*8; j+=8) {
			aa[i][j] = aa[i-1][j-1] + bb[i][j];
			aa[i][j+1] = aa[i-1][j+1-1] + bb[i][j+1];
			aa[i][j+2] = aa[i-1][j+2-1] + bb[i][j+2];
			aa[i][j+3] = aa[i-1][j+3-1] + bb[i][j+3];
			aa[i][j+4] = aa[i-1][j+4-1] + bb[i][j+4];
			aa[i][j+5] = aa[i-1][j+5-1] + bb[i][j+5];
			aa[i][j+6] = aa[i-1][j+6-1] + bb[i][j+6];
			aa[i][j+7] = aa[i-1][j+7-1] + bb[i][j+7];
		}
	}
	return 0;
}

int main() {
	return 0;
}