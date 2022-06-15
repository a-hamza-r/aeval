#include "declarations.h"

//	symbolics
//	symbolic dependence tests

int s171(int count, int inc) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8; i++) {
		a[i * inc] += b[i];
	}
  return 0;
}

