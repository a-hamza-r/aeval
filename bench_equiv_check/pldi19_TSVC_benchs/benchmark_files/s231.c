#include "declarations.h"

//	loop interchange
//	loop with data dependency

TYPE 
__attribute__((noinline))
s231(TYPE** aa, TYPE** bb, int count) {
	for (int j = 1; j < count*8; j++) {
		for (int i = 0; i < count*8; ++i) {
			aa[j][i] = aa[j - 1][i] + bb[j][i];
		}
	}
	return 0;
}

TYPE 
__attribute__((noinline))
s231_vec(TYPE** aa, TYPE** bb, int count) {
	for (int j = 1; j < count*8; j++) {
		for (int i = 0; i < count*8; i+=8) {
			aa[j][i] = aa[j - 1][i] + bb[j][i];
			aa[j][i+1] = aa[j - 1][i+1] + bb[j][i+1];
			aa[j][i+2] = aa[j - 1][i+2] + bb[j][i+2];
			aa[j][i+3] = aa[j - 1][i+3] + bb[j][i+3];
			aa[j][i+4] = aa[j - 1][i+4] + bb[j][i+4];
			aa[j][i+5] = aa[j - 1][i+5] + bb[j][i+5];
			aa[j][i+6] = aa[j - 1][i+6] + bb[j][i+6];
			aa[j][i+7] = aa[j - 1][i+7] + bb[j][i+7];
		}
	}
	return 0;
}

int main() {
	return 0;
}