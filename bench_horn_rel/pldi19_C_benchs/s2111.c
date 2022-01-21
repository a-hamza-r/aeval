#include "declarations.h"

//	wavefronts, it will make jump in data access

TYPE s2111(int count) {
	for (int j = 1; j < count*8; j++) {
		for (int i = 1; i < count*8; i++) {
			aa[j][i] = aa[j][i-1] + aa[j-1][i];
		}
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s2111(count);
}