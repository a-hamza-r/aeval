#include "declarations.h"

//	induction variable recognition
//	induction variable in two loops; collapsing possible

TYPE 
__attribute__((noinline))
s125(TYPE* array, TYPE** aa, TYPE **bb, TYPE **cc, int count) {
	for (int i = 0; i < count*8; i++) {
		for (int j = 0; j < count*8; j++) {
			array[i*count*8+j] = aa[i][j] + bb[i][j] * cc[i][j];
		}
	}
	return 0;
}

TYPE 
__attribute__((noinline))
s125_vec(TYPE* array, TYPE** aa, TYPE **bb, TYPE **cc, int count) {
	for (int i = 0; i < count*8; i++) {
		for (int j = 0; j < count*8; j+=8) {
			array[i*count*8+j] = aa[i][j] + bb[i][j] * cc[i][j];
			array[i*count*8+j+1] = aa[i][j+1] + bb[i][j+1] * cc[i][j+1];
			array[i*count*8+j+2] = aa[i][j+2] + bb[i][j+2] * cc[i][j+2];
			array[i*count*8+j+3] = aa[i][j+3] + bb[i][j+3] * cc[i][j+3];
			array[i*count*8+j+4] = aa[i][j+4] + bb[i][j+4] * cc[i][j+4];
			array[i*count*8+j+5] = aa[i][j+5] + bb[i][j+5] * cc[i][j+5];
			array[i*count*8+j+6] = aa[i][j+6] + bb[i][j+6] * cc[i][j+6];
			array[i*count*8+j+7] = aa[i][j+7] + bb[i][j+7] * cc[i][j+7];
		}
	}
	return 0;
}

int main() {
	return 0;
}