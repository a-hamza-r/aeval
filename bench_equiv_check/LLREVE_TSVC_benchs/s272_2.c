#include "declarations.h"

//	control flow
//	loop with independent conditional

int s272(int count, int t) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8; i+=8) {
		if (e[i] >= t) {
			a[i] += c[i] * d[i];
			b[i] += c[i] * c[i];
		}

		if (e[i+1] >= t) {
			a[i+1] += c[i+1] * d[i+1];
			b[i+1] += c[i+1] * c[i+1];
		}

		if (e[i+2] >= t) {
			a[i+2] += c[i+2] * d[i+2];
			b[i+2] += c[i+2] * c[i+2];
		}

		if (e[i+3] >= t) {
			a[i+3] += c[i+3] * d[i+3];
			b[i+3] += c[i+3] * c[i+3];
		}

		if (e[i+4] >= t) {
			a[i+4] += c[i+4] * d[i+4];
			b[i+4] += c[i+4] * c[i+4];
		}

		if (e[i+5] >= t) {
			a[i+5] += c[i+5] * d[i+5];
			b[i+5] += c[i+5] * c[i+5];
		}

		if (e[i+6] >= t) {
			a[i+6] += c[i+6] * d[i+6];
			b[i+6] += c[i+6] * c[i+6];
		}

		if (e[i+7] >= t) {
			a[i+7] += c[i+7] * d[i+7];
			b[i+7] += c[i+7] * c[i+7];
		}
	}
	return 0;
}

