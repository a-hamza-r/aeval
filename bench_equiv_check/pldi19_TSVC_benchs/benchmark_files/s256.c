#include "declarations.h"

//	scalar and array expansion
//	array expansion

TYPE 
__attribute__((noinline))
s256(TYPE* a, TYPE* d, TYPE **bb, TYPE **cc, int count) {
	for (int j = 1; j < count*8; j++) {
		a[j] = 1 - a[j - 1];
		for (int i = 0; i < count*8; i++) {
			cc[j][i] = a[j] + bb[j][i]*d[j];
	 	}
	}
	return 0;
}

TYPE 
__attribute__((noinline))
s256_vec(TYPE* a, TYPE* d, TYPE **bb, TYPE **cc, int count) {
	for (int j = 1; j < count*8; j++) {
		a[j] = 1 - a[j - 1];
		for (int i = 0; i < count*8; i+=8) {
			cc[j][i] = a[j] + bb[j][i]*d[j];
			cc[j][i+1] = a[j] + bb[j][i+1]*d[j];
			cc[j][i+2] = a[j] + bb[j][i+2]*d[j];
			cc[j][i+3] = a[j] + bb[j][i+3]*d[j];
			cc[j][i+4] = a[j] + bb[j][i+4]*d[j];
			cc[j][i+5] = a[j] + bb[j][i+5]*d[j];
			cc[j][i+6] = a[j] + bb[j][i+6]*d[j];
			cc[j][i+7] = a[j] + bb[j][i+7]*d[j];
	 	}
	}
	return 0;
}

int main() {
	return 0;
}