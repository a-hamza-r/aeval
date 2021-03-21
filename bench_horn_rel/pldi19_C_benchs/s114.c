#include "declarations.h"


TYPE s114(int count) {
	for (int i = 0; i < count; i++) {
		for (int j = 0; j < i; j++) {
			aa[i][j] = aa[j][i] + bb[i][j];
		}
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s114(count);
}