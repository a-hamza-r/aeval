#include "declarations.h"

//	scalar and array expansion
//	scalar expansion

int s1251(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 0; i < count*8; i++) {
    s[i] = b[i]+c[i];
    b[i] = a[i]+d[i];
    a[i] = s[i]*e[i];
  }
  return 0;
}


