#include "declarations.h"

//	loop peeling
//	a(i)=a(0) with actual dependence cycle, loop is vectorizable

int s293(int count) {
if (count <= 0 || count > 10) return 1;
	TYPE t = a[0];
	a[0] = t;
	a[1] = t;
	a[2] = t;
	a[3] = t;
	a[4] = t;
	a[5] = t;
	a[6] = t;
	a[7] = t;
	for (int i = 8; i < count*8; i+=8) {
		a[i] = t;
		a[i+1] = t;
		a[i+2] = t;
		a[i+3] = t;
		a[i+4] = t;
		a[i+5] = t;
		a[i+6] = t;
		a[i+7] = t;
	}
  return 0;
}

