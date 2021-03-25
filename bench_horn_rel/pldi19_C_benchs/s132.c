#include "declarations.h"

//	global data flow analysis
//	loop with multiple dimension ambiguous subscripts

TYPE s132(int count) {
	int m = 0;
	int j = m;
	int k = m+1;
	for (int i= 1; i < count; i++) {
		aa[j][i] = aa[k][i-1] + b[i] * c[1];
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s132(count);
}