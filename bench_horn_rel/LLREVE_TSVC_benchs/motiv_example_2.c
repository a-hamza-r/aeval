#include "declarations.h"

int motiv_example(int count) {
if (count <= 0 || count > 10) return 1;
	int b0 = b[0];
	if (b0 > 0) {
		a[0] = a[1] + b[0];
		a[1] = a[2] + b[1];
	}
  for (int i = 2; i < count*4-2; i+=4) {
  	if (b0 > 0) {
			a[i] = a[i+1] + b[i];
			a[i+1] = a[i+1+1] + b[i+1];
			a[i+2] = a[i+2+1] + b[i+2];
			a[i+3] = a[i+3+1] + b[i+3];
  	}
  }
	if (b0 > 0)
		a[count*4-2] = a[count*4-1] + b[count*4-2];
  return 0;
}

