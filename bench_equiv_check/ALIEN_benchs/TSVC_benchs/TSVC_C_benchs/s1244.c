#include "declarations.h"

//	node splitting
//	cycle with ture and anti dependency

TYPE s1244(int count) {
	for (int i = 0; i < count*8-1; i++) {
		a[i] = b[i] + c[i] * c[i] + b[i]*b[i] + c[i];
		d[i] = a[i] + a[i+1];
	}
  return 0;
}

/*after node splitting:

TYPE s1244(int count) {
	for (int i = 0; i < count*8-1; i++) {
		TYPE t = a[i+1];
		a[i] = b[i] + c[i] * c[i] + b[i]*b[i] + c[i];
		d[i] = a[i] + t;
	}
  return 0;
}*/

int nondet();

int main() {
	int count = nondet();
	s1244(count);
}