#include "declarations.h"

//	control flow
//	if to elemental min

TYPE s2712(int count) {
	for (int i = 0; i < count*8; i++) {
		if (a[i] > b[i]) {
			a[i] += b[i] * c[i];
		}
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s2712(count);
}