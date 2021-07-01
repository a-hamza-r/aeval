#include "declarations.h"

//	symbolics
//	loop with subscript that may seem ambiguous

TYPE s174(int M) {
	for (int i = 0; i < M; i++) {
		a[i+M] = a[i] + b[i];
	}
  return 0;
}


int nondet();

int main() {
	int M = nondet();
	s174(M);
}