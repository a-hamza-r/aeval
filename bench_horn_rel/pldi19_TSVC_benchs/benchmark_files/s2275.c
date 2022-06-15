#include "declarations.h"

//	loop distribution is needed to be able to interchange

TYPE 
__attribute__((noinline))
s2275(TYPE* a, TYPE* b, TYPE *c, TYPE *d, TYPE **aa, TYPE **bb, TYPE **cc, int count) {
	for (int j = 0; j < count*8; j++) {
		for (int i = 0; i < count*8; i++) {
			aa[j][i] = aa[j][i] + bb[j][i] * cc[j][i];
		}
		a[j] = b[j] + c[j] * d[j];
	}
  return 0;
}

TYPE 
__attribute__((noinline))
s2275_vec(TYPE* a, TYPE* b, TYPE *c, TYPE *d, TYPE **aa, TYPE **bb, TYPE **cc, int count) {
	for (int j = 0; j < count*8; j++) {
		for (int i = 0; i < count*8; i+=8) {
			aa[j][i] = aa[j][i] + bb[j][i] * cc[j][i];
			aa[j][i+1] = aa[j][i+1] + bb[j][i+1] * cc[j][i+1];
			aa[j][i+2] = aa[j][i+2] + bb[j][i+2] * cc[j][i+2];
			aa[j][i+3] = aa[j][i+3] + bb[j][i+3] * cc[j][i+3];
			aa[j][i+4] = aa[j][i+4] + bb[j][i+4] * cc[j][i+4];
			aa[j][i+5] = aa[j][i+5] + bb[j][i+5] * cc[j][i+5];
			aa[j][i+6] = aa[j][i+6] + bb[j][i+6] * cc[j][i+6];
			aa[j][i+7] = aa[j][i+7] + bb[j][i+7] * cc[j][i+7];
		}
		a[j] = b[j] + c[j] * d[j];
	}
  return 0;
}

int main() {
	return 0;
}