#include "declarations.h"


TYPE s312(int count) {
	TYPE prod = 1;
	for (int i = 0; i < count*8; i++) {
		prod *= a[i];
	}
	return prod;
}


int nondet();

int main() {
	int count = nondet();
	s312(count);
}