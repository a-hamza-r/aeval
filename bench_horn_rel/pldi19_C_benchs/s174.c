#include "declarations.h"


TYPE s174(int count, int M) {
	for (int i = 0; i < M; i++) {
		a[i+M] = a[i] + b[i];
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	int M = nondet();
	s174(count, M);
}