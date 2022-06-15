#include "declarations.h"

//	statement reordering
//	dependency needing temporary

int s1213(int count) {
if (count <= 0 || count > 10) return 1;
	b[1] = a[1+1]*d[1];
	a[1] = b[1-1]+c[1];

	b[2] = a[2+1]*d[2];
	a[2] = b[2-1]+c[2];

	b[3] = a[3+1]*d[3];
	a[3] = b[3-1]+c[3];

	b[4] = a[4+1]*d[4];
	a[4] = b[4-1]+c[4];

	b[5] = a[5+1]*d[5];
	a[5] = b[5-1]+c[5];

	b[6] = a[6+1]*d[6];
	a[6] = b[6-1]+c[6];

	for (int i = 7; i < count*8-1; i+=8) {
		b[i] = a[i+1]*d[i];
		a[i] = b[i-1]+c[i];

		b[i+1] = a[i+1+1]*d[i+1];
		a[i+1] = b[i+1-1]+c[i+1];

		b[i+2] = a[i+2+1]*d[i+2];
		a[i+2] = b[i+2-1]+c[i+2];

		b[i+3] = a[i+3+1]*d[i+3];
		a[i+3] = b[i+3-1]+c[i+3];

		b[i+4] = a[i+4+1]*d[i+4];
		a[i+4] = b[i+4-1]+c[i+4];

		b[i+5] = a[i+5+1]*d[i+5];
		a[i+5] = b[i+5-1]+c[i+5];

		b[i+6] = a[i+6+1]*d[i+6];
		a[i+6] = b[i+6-1]+c[i+6];

		b[i+7] = a[i+7+1]*d[i+7];
		a[i+7] = b[i+7-1]+c[i+7];
	}
  return 0;
}

