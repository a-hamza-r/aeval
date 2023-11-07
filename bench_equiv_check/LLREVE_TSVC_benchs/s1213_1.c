#include "declarations.h"

//	statement reordering
//	dependency needing temporary

int s1213(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 1; i < count*8-1; i++) {
		b[i] = a[i+1]*d[i];
		a[i] = b[i-1]+c[i];
	}
  return 0;
}
