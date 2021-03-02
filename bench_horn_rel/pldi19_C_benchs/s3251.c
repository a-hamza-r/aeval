#include "declarations.h"


TYPE s3251(int count) {
  TYPE s;
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