#include "declarations.h"


TYPE s1119(int count) {
	for (int i = 1; i < count; i++) {
		for (int j = 0; j < count; j++) {
			aa[i][j] = aa[i-1][j] + bb[i][j];
		}
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s1119(count);
}