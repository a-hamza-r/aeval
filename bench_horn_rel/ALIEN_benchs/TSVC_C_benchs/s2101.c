#include "declarations.h"

//	diagonals
//	main diagonal calculation
//	jump in data access

TYPE s2101(int count) {
	for (int i = 0; i < count*8; i++) {
		aa[i][i] += bb[i][i] * cc[i][i];
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s2101(count);
}