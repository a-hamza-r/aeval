#include "declarations.h"

//	control flow
//	semantic if removal

TYPE s2711(int count) {
	for (int i = 0; i < count*8; i++) {
		if (b[i] != (float)0.0) {
			a[i] += b[i] * c[i];
		}
	}
  return 0;
}


/*after if removal:

TYPE s2711(int count) {
	for (int i = 0; i < count*8; i++) {
			a[i] += b[i] * c[i];
	}
  return 0;
}*/


int nondet();

int main() {
	int count = nondet();
	s2711(count);
}