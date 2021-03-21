#include "declarations.h"


TYPE s126(int count) {
	int k = 1;
	for (int i = 0; i < count; i++) {
		for (int j = 1; j < count; j++) {
			bb[j][i] = bb[j-1][i] + array[k-1] * cc[j][i];
			++k;
		}
		++k;
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s126(count);
}