#include "declarations.h"


TYPE s119(int count) {
	for (int i = 1; i < count; i++) {
		for (int j = 1; j < count; j++) {
			aa[i][j] = aa[i-1][j-1] + bb[i][j];
		}
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s119(count);
}