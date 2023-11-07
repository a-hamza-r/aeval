#include "declarations.h"

//	node splitting
//	false dependence cycle breaking


TYPE 
__attribute__((noinline))
s243(TYPE* a, TYPE* b, TYPE *c, TYPE *d, TYPE *e, int count) {
  TYPE f[count*8-1];
  for (int i = 0; i < count*8-1; i++) {
    f[i] = a[i+1];
    a[i] = b[i] + c[i  ] * d[i];
    b[i] = a[i] + d[i  ] * e[i];
    a[i] = b[i] + f[i] * d[i];
  }
  return 0;
}

TYPE 
__attribute__((noinline))
s243_vec(TYPE* a, TYPE* b, TYPE *c, TYPE *d, TYPE *e, int count) {
  TYPE f[count*8-1];
  if (count > 0) {
  f[0] = a[0+1];
  a[0] = b[0] + c[0  ] * d[0];
  b[0] = a[0] + d[0  ] * e[0];
  a[0] = b[0] + f[0] * d[0];

  f[1] = a[1+1];
  a[1] = b[1] + c[1  ] * d[1];
  b[1] = a[1] + d[1  ] * e[1];
  a[1] = b[1] + f[1] * d[1];

  f[2] = a[2+1];
  a[2] = b[2] + c[2  ] * d[2];
  b[2] = a[2] + d[2  ] * e[2];
  a[2] = b[2] + f[2] * d[2];

  f[3] = a[3+1];
  a[3] = b[3] + c[3  ] * d[3];
  b[3] = a[3] + d[3  ] * e[3];
  a[3] = b[3] + f[3] * d[3];

  f[4] = a[4+1];
  a[4] = b[4] + c[4  ] * d[4];
  b[4] = a[4] + d[4  ] * e[4];
  a[4] = b[4] + f[4] * d[4];

  f[5] = a[5+1];
  a[5] = b[5] + c[5  ] * d[5];
  b[5] = a[5] + d[5  ] * e[5];
  a[5] = b[5] + f[5] * d[5];

  f[6] = a[6+1];
  a[6] = b[6] + c[6  ] * d[6];
  b[6] = a[6] + d[6  ] * e[6];
  a[6] = b[6] + f[6] * d[6];
}

  for (int i = 7; i < count*8-1; i+=8) {
    f[i] = a[i+1];
    a[i] = b[i] + c[i  ] * d[i];
    b[i] = a[i] + d[i  ] * e[i];
    a[i] = b[i] + f[i] * d[i];

    f[i+1] = a[i+1+1];
    a[i+1] = b[i+1] + c[i+1  ] * d[i+1];
    b[i+1] = a[i+1] + d[i+1  ] * e[i+1];
    a[i+1] = b[i+1] + f[i+1] * d[i+1];

    f[i+2] = a[i+2+1];
    a[i+2] = b[i+2] + c[i+2  ] * d[i+2];
    b[i+2] = a[i+2] + d[i+2  ] * e[i+2];
    a[i+2] = b[i+2] + f[i+2] * d[i+2];

    f[i+3] = a[i+3+1];
    a[i+3] = b[i+3] + c[i+3  ] * d[i+3];
    b[i+3] = a[i+3] + d[i+3  ] * e[i+3];
    a[i+3] = b[i+3] + f[i+3] * d[i+3];

    f[i+4] = a[i+4+1];
    a[i+4] = b[i+4] + c[i+4  ] * d[i+4];
    b[i+4] = a[i+4] + d[i+4  ] * e[i+4];
    a[i+4] = b[i+4] + f[i+4] * d[i+4];

    f[i+5] = a[i+5+1];
    a[i+5] = b[i+5] + c[i+5  ] * d[i+5];
    b[i+5] = a[i+5] + d[i+5  ] * e[i+5];
    a[i+5] = b[i+5] + f[i+5] * d[i+5];

    f[i+6] = a[i+6+1];
    a[i+6] = b[i+6] + c[i+6  ] * d[i+6];
    b[i+6] = a[i+6] + d[i+6  ] * e[i+6];
    a[i+6] = b[i+6] + f[i+6] * d[i+6];

    f[i+7] = a[i+7+1];
    a[i+7] = b[i+7] + c[i+7  ] * d[i+7];
    b[i+7] = a[i+7] + d[i+7  ] * e[i+7];
    a[i+7] = b[i+7] + f[i+7] * d[i+7];
  }
  return 0;
}

int main() {
  return 0;
}