#include "declarations.h"

//	scalar and array expansion
//	scalar expansion assigned under if

int s253(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8; i+=8) {
		if (a[i] > b[i]) {
			s[i] = a[i] - b[i] * d[i];
			c[i] += s[i];
			a[i] = s[i];
		}

		if (a[i+1] > b[i+1]) {
			s[i+1] = a[i+1] - b[i+1] * d[i+1];
			c[i+1] += s[i+1];
			a[i+1] = s[i+1];
		}

		if (a[i+2] > b[i+2]) {
			s[i+2] = a[i+2] - b[i+2] * d[i+2];
			c[i+2] += s[i+2];
			a[i+2] = s[i+2];
		}

		if (a[i+3] > b[i+3]) {
			s[i+3] = a[i+3] - b[i+3] * d[i+3];
			c[i+3] += s[i+3];
			a[i+3] = s[i+3];
		}

		if (a[i+4] > b[i+4]) {
			s[i+4] = a[i+4] - b[i+4] * d[i+4];
			c[i+4] += s[i+4];
			a[i+4] = s[i+4];
		}

		if (a[i+5] > b[i+5]) {
			s[i+5] = a[i+5] - b[i+5] * d[i+5];
			c[i+5] += s[i+5];
			a[i+5] = s[i+5];
		}

		if (a[i+6] > b[i+6]) {
			s[i+6] = a[i+6] - b[i+6] * d[i+6];
			c[i+6] += s[i+6];
			a[i+6] = s[i+6];
		}

		if (a[i+7] > b[i+7]) {
			s[i+7] = a[i+7] - b[i+7] * d[i+7];
			c[i+7] += s[i+7];
			a[i+7] = s[i+7];
		}
	}
  return 0;
}

