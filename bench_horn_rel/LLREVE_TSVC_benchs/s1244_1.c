#include "declarations.h"

//	node splitting
//	cycle with ture and anti dependency

int s1244(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8-1; i++) {
		TYPE t = a[i+1];
		a[i] = b[i] + c[i] * c[i] + b[i]*b[i] + c[i];
		d[i] = a[i] + t;
	}
  return 0;
}
