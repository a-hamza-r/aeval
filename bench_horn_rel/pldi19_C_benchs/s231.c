#include "declarations.h"


TYPE s000(int count) {
	for (int i = 0; i < count; ++i) {
		for (int j = 1; j < count; j++) {
			aa[j][i] = aa[j - 1][i] + bb[j][i];
		}
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s000(count);
}