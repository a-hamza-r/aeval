#include "declarations.h"


TYPE s1281(int count) {
	for (int i = 0; i < count*8; i++) {
		x = b[i]*c[i]+a[i]*d[i]+e[i];
		a[i] = x-(float)1.0;
		b[i] = x;
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s1281(count);
}