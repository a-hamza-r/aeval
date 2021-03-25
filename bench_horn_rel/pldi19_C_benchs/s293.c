#include "declarations.h"

//	loop peeling
//	a(i)=a(0) with actual dependence cycle, loop is vectorizable

TYPE s293(int count) {
	for (int i = 0; i < count*8; i++) {
		a[i] = a[0];
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s293(count);
}