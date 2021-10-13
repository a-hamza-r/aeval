#include "declarations.h"

//	loop peeling
//	a(i)=a(0) with actual dependence cycle, loop is vectorizable

int s293(int count) {
if (count <= 0 || count > 10) return 1;
	TYPE t = a[0];
	a[0] = t;
	for (int i = 1; i < count*8; i++) {
		a[i] = t;
	}
  return 0;
}

