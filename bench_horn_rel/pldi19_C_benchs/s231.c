#include "declarations.h"

//	loop interchange
//	loop with data dependency

TYPE s231(int count) {
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
	s231(count);
}