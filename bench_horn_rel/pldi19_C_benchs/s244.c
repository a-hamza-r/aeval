#include "declarations.h"

//	node splitting
//	false dependence cycle breaking

TYPE s244(int count) {
	for (int i = 0; i < count*8-1; ++i) {
		a[i] = b[i] + c[i] * d[i];
		b[i] = c[i] + b[i];
		a[i+1] = b[i] + a[i+1] * d[i];
	}
  return 0;
}


/*after transformation:

TYPE s244(int count) {
	for (int i = 0; i < count*8-1; ++i) {
		a[i+1] = c[i] + b[i] + a[i+1] * d[i];
		a[i] = b[i] + c[i] * d[i];
		b[i] = c[i] + b[i];
	}
  return 0;
}*/

int nondet();

int main() {
	int count = nondet();
	s244(count);
}