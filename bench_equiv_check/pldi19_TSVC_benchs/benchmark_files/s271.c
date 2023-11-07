#include "declarations.h"

//	control flow
//	loop with singularity handling

TYPE 
__attribute__((noinline))
s271(TYPE* a, TYPE* b, TYPE *c, int count) {
	for (int i = 0; i < count*8; i++) {
		if (b[i] > 0) {
			a[i] += b[i] * c[i];
		}
	}
  return 0;
}

TYPE 
__attribute__((noinline))
s271_vec(TYPE* a, TYPE* b, TYPE *c, int count) {
	for (int i = 0; i < count*8; i++) {
		if (b[i] > 0) {
			a[i] += b[i] * c[i];
		}

		if (b[i+1] > 0) {
			a[i+1] += b[i+1] * c[i+1];
		}

		if (b[i+2] > 0) {
			a[i+2] += b[i+2] * c[i+2];
		}

		if (b[i+3] > 0) {
			a[i+3] += b[i+3] * c[i+3];
		}

		if (b[i+4] > 0) {
			a[i+4] += b[i+4] * c[i+4];
		}

		if (b[i+5] > 0) {
			a[i+5] += b[i+5] * c[i+5];
		}

		if (b[i+6] > 0) {
			a[i+6] += b[i+6] * c[i+6];
		}

		if (b[i+7] > 0) {
			a[i+7] += b[i+7] * c[i+7];
		}
	}
  return 0;
}

int main() {
	return 0;
}