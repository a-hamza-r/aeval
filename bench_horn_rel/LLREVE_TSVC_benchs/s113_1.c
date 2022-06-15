#include "declarations.h"

//	linear dependence testing
//	a(i)=a(1) but no actual dependence cycle

int s113(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 1; i < count*8; i++) {
		a[i] = a[0] + b[i];
	}
	return 0;
}
