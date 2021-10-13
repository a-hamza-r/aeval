#include "declarations.h"

//	statement reordering
//	statement reordering allows vectorization

int s211(int count) {
if (count <= 0 || count > 10) return 1;
	b[1] = b[1 + 1] - e[1] * d[1];
	a[1] = b[1 - 1] + c[1] * d[1];

	b[1+1] = b[1+1 + 1] - e[1+1] * d[1+1];
	a[1+1] = b[1+1 - 1] + c[1+1] * d[1+1];

	b[1+2] = b[1+2 + 1] - e[1+2] * d[1+2];
	a[1+2] = b[1+2 - 1] + c[1+2] * d[1+2];

	b[1+3] = b[1+3 + 1] - e[1+3] * d[1+3];
	a[1+3] = b[1+3 - 1] + c[1+3] * d[1+3];

	b[1+4] = b[1+4 + 1] - e[1+4] * d[1+4];
	a[1+4] = b[1+4 - 1] + c[1+4] * d[1+4];

	b[1+5] = b[1+5 + 1] - e[1+5] * d[1+5];
	a[1+5] = b[1+5 - 1] + c[1+5] * d[1+5];

	for (int i = 7; i < count*8-1; i+=8) {
		b[i] = b[i + 1] - e[i] * d[i];
		a[i] = b[i - 1] + c[i] * d[i];

		b[i+1] = b[i+1 + 1] - e[i+1] * d[i+1];
		a[i+1] = b[i+1 - 1] + c[i+1] * d[i+1];

		b[i+2] = b[i+2 + 1] - e[i+2] * d[i+2];
		a[i+2] = b[i+2 - 1] + c[i+2] * d[i+2];

		b[i+3] = b[i+3 + 1] - e[i+3] * d[i+3];
		a[i+3] = b[i+3 - 1] + c[i+3] * d[i+3];

		b[i+4] = b[i+4 + 1] - e[i+4] * d[i+4];
		a[i+4] = b[i+4 - 1] + c[i+4] * d[i+4];

		b[i+5] = b[i+5 + 1] - e[i+5] * d[i+5];
		a[i+5] = b[i+5 - 1] + c[i+5] * d[i+5];

		b[i+6] = b[i+6 + 1] - e[i+6] * d[i+6];
		a[i+6] = b[i+6 - 1] + c[i+6] * d[i+6];

		b[i+7] = b[i+7 + 1] - e[i+7] * d[i+7];
		a[i+7] = b[i+7 - 1] + c[i+7] * d[i+7];
	}
	return 0;
}

