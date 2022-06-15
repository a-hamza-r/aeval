#include "declarations.h"

//	linear dependence testing
//	a(i)=a(1) but no actual dependence cycle

int s113(int count) {
if (count <= 0 || count > 10) return 1;
	a[1] = a[0] + b[1];
	a[2] = a[0] + b[2];
	a[3] = a[0] + b[3];
	a[4] = a[0] + b[4];
	a[5] = a[0] + b[5];
	a[6] = a[0] + b[6];
	a[7] = a[0] + b[7];
	for (int i = 8; i < count*8; i+=8) {
		a[i] = a[0] + b[i];
		a[i+1] = a[0] + b[i+1];
		a[i+2] = a[0] + b[i+2];
		a[i+3] = a[0] + b[i+3];
		a[i+4] = a[0] + b[i+4];
		a[i+5] = a[0] + b[i+5];
		a[i+6] = a[0] + b[i+6];
		a[i+7] = a[0] + b[i+7];
	}
	return 0;
}
