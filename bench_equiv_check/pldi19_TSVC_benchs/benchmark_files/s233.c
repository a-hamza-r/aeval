#include "declarations.h"

//	loop interchange
//	interchanging with one of two inner loops

TYPE s233(int count) {
	for (int i = 1; i < count; i++) {
		for (int j = 1; j < count; j++) {
			aa[j][i] = aa[j-1][i] + cc[j][i];
		}
		for (int j = 1; j < count; j++) {
			bb[j][i] = bb[j][i-1] + cc[j][i];
		}
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s233(count);
}