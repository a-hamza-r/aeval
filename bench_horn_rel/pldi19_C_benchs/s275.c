#include "declarations.h"

//	control flow
//	if around inner loop, interchanging needed

TYPE s275(int count) {
	for (int i = 0; i < count; i++) {
		if (aa[0][i] > (float)0.) {
			for (int j = 1; j < count; j++) {
				aa[j][i] = aa[j-1][i] + bb[j][i] * cc[j][i];
			}
		}
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s275(count);
}