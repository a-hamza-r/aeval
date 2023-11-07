#include "declarations.h"

//	linear dependence testing
//	potential dot product recursion

TYPE s118(int count) {
	for (int i = 1; i < count; i++) {
		for (int j = 0; j <= i - 1; j++) {
			a[i] += bb[j][i] * a[i-j-1];
		}
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s118(count);
}