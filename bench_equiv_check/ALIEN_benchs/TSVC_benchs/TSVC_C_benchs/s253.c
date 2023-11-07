#include "declarations.h"

//	scalar and array expansion
//	scalar expansion assigned under if

TYPE s253(int count) {
	int s;
	for (int i = 0; i < count*8; i++) {
		if (a[i] > b[i]) {
			s = a[i] - b[i] * d[i];
			c[i] += s;
			a[i] = s;
		}
	}
  return 0;
}

/*after scalar and array expansion:

TYPE s253(int count) {
	int s[count*8];
	for (int i = 0; i < count*8; i++) {
		if (a[i] > b[i]) {
			s[i] = a[i] - b[i] * d[i];
			c[i] += s[i];
			a[i] = s[i];
		}
	}
  return 0;
}*/


int nondet();

int main() {
	int count = nondet();
	s253(count);
}