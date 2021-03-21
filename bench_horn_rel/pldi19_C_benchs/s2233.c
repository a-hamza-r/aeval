#include "declarations.h"


TYPE s2233(int count) {
	for (int i = 1; i < count; i++) {
		for (int j = 1; j < count; j++) {
			aa[j][i] = aa[j-1][i] + cc[j][i];
		}
		for (int j = 1; j < count; j++) {
			bb[i][j] = bb[i-1][j] + cc[i][j];
		}
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s2233(count);
}