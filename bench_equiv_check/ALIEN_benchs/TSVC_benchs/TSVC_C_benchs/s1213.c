#include "declarations.h"

//	statement reordering
//	dependency needing temporary

TYPE s1213(int count) {
	for (int i = 1; i < count*8-1; i++) {
		a[i] = b[i-1]+c[i];
		b[i] = a[i+1]*d[i];
	}
  return 0;
}

/*after statement reordering:

TYPE s1213(int count) {
	for (int i = 1; i < count*8-1; i++) {
		b[i] = a[i+1]*d[i];
		a[i] = b[i-1]+c[i];
	}
  return 0;
}*/


int nondet();

int main() {
	int count = nondet();
	s1213(count);
}