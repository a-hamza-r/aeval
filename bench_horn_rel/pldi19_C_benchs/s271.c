#include "declarations.h"


TYPE s271(int count) {
	for (int i = 0; i < count*8; i++) {
		if (b[i] > (float)0.) {
			a[i] += b[i] * c[i];
		}
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s271(count);
}