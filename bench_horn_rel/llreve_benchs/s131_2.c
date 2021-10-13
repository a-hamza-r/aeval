#include "declarations.h"

//	global data flow analysis
//	forward substitution

int s131(int count) {
if (count <= 0 || count > 10) return 1;
	a[0] = a[0 + 1] + b[0];
	a[0+1] = a[0+1 + 1] + b[0+1];
	a[0+2] = a[0+2 + 1] + b[0+2];
	a[0+3] = a[0+3 + 1] + b[0+3];
	a[0+4] = a[0+4 + 1] + b[0+4];
	a[0+5] = a[0+5 + 1] + b[0+5];
	a[0+6] = a[0+6 + 1] + b[0+6];
	for (int i = 7; i < count*8 - 1; i+=8) {
		a[i] = a[i + 1] + b[i];
		a[i+1] = a[i+1 + 1] + b[i+1];
		a[i+2] = a[i+2 + 1] + b[i+2];
		a[i+3] = a[i+3 + 1] + b[i+3];
		a[i+4] = a[i+4 + 1] + b[i+4];
		a[i+5] = a[i+5 + 1] + b[i+5];
		a[i+6] = a[i+6 + 1] + b[i+6];
		a[i+7] = a[i+7 + 1] + b[i+7];
	}
	return 0;
}

