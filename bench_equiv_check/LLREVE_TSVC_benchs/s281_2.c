#include "declarations.h"

//	crossing thresholds
//	index set splitting
//	reverse data access

int s281(int count) {
if (count <= 0 || count > 10) return 1;
	for (int i = 0; i < count*8; i+=8) {
		e[i] = a[count*8-i-1] + b[i] * c[i];
		a[i] = e[i]-1;
		b[i] = e[i];

		e[(i+1)] = a[count*8-(i+1)-1] + b[(i+1)] * c[(i+1)];
		a[(i+1)] = e[(i+1)]-1;
		b[(i+1)] = e[(i+1)];

		e[(i+2)] = a[count*8-(i+2)-1] + b[(i+2)] * c[(i+2)];
		a[(i+2)] = e[(i+2)]-1;
		b[(i+2)] = e[(i+2)];

		e[(i+3)] = a[count*8-(i+3)-1] + b[(i+3)] * c[(i+3)];
		a[(i+3)] = e[(i+3)]-1;
		b[(i+3)] = e[(i+3)];

		e[(i+4)] = a[count*8-(i+4)-1] + b[(i+4)] * c[(i+4)];
		a[(i+4)] = e[(i+4)]-1;
		b[(i+4)] = e[(i+4)];

		e[(i+5)] = a[count*8-(i+5)-1] + b[(i+5)] * c[(i+5)];
		a[(i+5)] = e[(i+5)]-1;
		b[(i+5)] = e[(i+5)];

		e[(i+4)] = a[count*8-(i+4)-1] + b[(i+4)] * c[(i+4)];
		a[(i+4)] = e[(i+4)]-1;
		b[(i+4)] = e[(i+4)];

		e[(i+5)] = a[count*8-(i+5)-1] + b[(i+5)] * c[(i+5)];
		a[(i+5)] = e[(i+5)]-1;
		b[(i+5)] = e[(i+5)];

		e[(i+6)] = a[count*8-(i+6)-1] + b[(i+6)] * c[(i+6)];
		a[(i+6)] = e[(i+6)]-1;
		b[(i+6)] = e[(i+6)];	
		
		e[(i+7)] = a[count*8-(i+7)-1] + b[(i+7)] * c[(i+7)];
		a[(i+7)] = e[(i+7)]-1;
		b[(i+7)] = e[(i+7)];	
	}
  return 0;
}

