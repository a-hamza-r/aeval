#include "declarations.h"

//    non-logical if's
//    arithmetic if

int s441(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 0; i < count*8; i++) {
    if (d[i] < 0) {
        a[i] += b[i] * c[i];
    } else if (d[i] == 0) {
        a[i] += b[i] * b[i];
    } else {
        a[i] += c[i] * c[i];
    }
  }
  return 0;
}

