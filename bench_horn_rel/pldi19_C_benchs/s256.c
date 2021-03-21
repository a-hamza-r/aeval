#include "declarations.h"


TYPE s256(int count) {
	for (int i = 0; i < count; i++) {
		for (int j = 1; j < count; j++) {
			a[j] = (float)1.0 - a[j - 1];
			cc[j][i] = a[j] + bb[j][i]*d[j];
		}
	}
	return 0;
}


int nondet();

int main() {
	int count = nondet();
	s256(count);
}