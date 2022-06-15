#include "declarations.h"

//    recurrences
//    coupled recurrence

int s323(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 1; i < count*8; i++) {
    a[i] = b[i-1] + c[i] * d[i];
    b[i] = a[i] + c[i] * e[i];
  }
  return 0;
}

