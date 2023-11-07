#include "declarations.h"

//	scalar and array expansion
//	scalar expansion

int s2251(int count) {
if (count <= 0 || count > 10) return 1;
	s[0] = 0;
	for (int i = 0; i < count*8; i++) {
		a[i] = s[i]*e[i];
		s[i+1] = b[i]+c[i];
		b[i] = a[i]+d[i];
	}
	return 0;
}


