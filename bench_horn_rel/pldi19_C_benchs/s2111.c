#include "declarations.h"


TYPE s2111(int count) {
	for (int j = 1; j < count; j++) {
		for (int i = 1; i < count; i++) {
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