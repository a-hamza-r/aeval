#include "declarations.h"

//	scalar and array expansion
//	scalar expansion

TYPE s3251(int count) {
  for (int i = 0; i < count*8-1; i++) {
		a[i+1] = b[i]+c[i];
		b[i]   = c[i]*e[i];
		d[i]   = a[i]*e[i];
  }
  return 0;
}


int nondet();

int main() {
  int count = nondet();
  s3251(count);
}