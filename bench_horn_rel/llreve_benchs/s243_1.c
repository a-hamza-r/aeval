#include "declarations.h"

//	node splitting
//	false dependence cycle breaking

int s243(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 0; i < count*8-1; i++) {
    f[i] = a[i+1];
    a[i] = b[i] + c[i  ] * d[i];
    b[i] = a[i] + d[i  ] * e[i];
    a[i] = b[i] + f[i] * d[i];
  }
  return 0;
}

