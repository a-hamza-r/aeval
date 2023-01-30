#include "declarations.h"

//	symbolics
//	vectorizable if n3 .ne. 0

TYPE s172(int count, int n1, int n3) {
	for (int i = n1-1; i < count*8; i += n3) {
		a[i] += b[i];
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	int n1 = nondet();
	int n3 = nondet();
	s172(count, n1, n3);
}