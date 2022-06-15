#include "declarations.h"

//	induction variable recognition
//	induction variable in two loops; recurrence in inner loop

TYPE 
__attribute__((noinline))
s126(TYPE* array, TYPE **bb, TYPE **cc, int count) {
	for (int j = 1; j < count*8; j++) {
		for (int i = 0; i < count*8; i++) {
			bb[j][i] = bb[j-1][i] + array[i+j-1] * cc[j][i];
		}
	}
	return 0;
}

TYPE 
__attribute__((noinline))
s126_vec(TYPE* array, TYPE **bb, TYPE **cc, int count) {
	for (int j = 1; j < count*8; j++) {
		for (int i = 0; i < count*8; i+=8) {
			bb[j][i] = bb[j-1][i] + array[i+j-1] * cc[j][i];
			bb[j][i+1] = bb[j-1][i+1] + array[i+1+j-1] * cc[j][i+1];
			bb[j][i+2] = bb[j-1][i+2] + array[i+2+j-1] * cc[j][i+2];
			bb[j][i+3] = bb[j-1][i+3] + array[i+3+j-1] * cc[j][i+3];
			bb[j][i+4] = bb[j-1][i+4] + array[i+4+j-1] * cc[j][i+4];
			bb[j][i+5] = bb[j-1][i+5] + array[i+5+j-1] * cc[j][i+5];
			bb[j][i+6] = bb[j-1][i+6] + array[i+6+j-1] * cc[j][i+6];
			bb[j][i+7] = bb[j-1][i+7] + array[i+7+j-1] * cc[j][i+7];
		}
	}
	return 0;
}

int main() {
	return 0;
}