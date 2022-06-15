#include "declarations.h"

//	loop interchange
//	interchanging of triangular loops

TYPE s1232(int count) {
	for (int j = 0; j < count; j++) {
		for (int i = j; i < count; i++) {
			aa[i][j] = bb[i][j] + cc[i][j];
		}
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s1232(count);
}