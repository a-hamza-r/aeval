#include "declarations.h"


TYPE s312(int count) {
if (count <= 0 || count > 10) return 1;
	TYPE prod = 1;
	for (int i = 0; i < count*8; i+=8) {
		prod *= a[i];
		prod *= a[i+1];
		prod *= a[i+2];
		prod *= a[i+3];
		prod *= a[i+4];
		prod *= a[i+5];
		prod *= a[i+6];
		prod *= a[i+7];
	}
	return prod;
}

