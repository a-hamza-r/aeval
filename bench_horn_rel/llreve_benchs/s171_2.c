#include "declarations.h"

//	symbolics
//	symbolic dependence tests

int s171(int count, int inc) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8; i+=8) {
		a[i * inc] += b[i];
		a[(i+1) * inc] += b[(i+1)];
		a[(i+2) * inc] += b[(i+2)];
		a[(i+3) * inc] += b[(i+3)];
		a[(i+4) * inc] += b[(i+4)];
		a[(i+5) * inc] += b[(i+5)];
		a[(i+6) * inc] += b[(i+6)];
		a[(i+7) * inc] += b[(i+7)];
	}
  return 0;
}

