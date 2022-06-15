#include "declarations.h"

//    control loops
//    vector assignment, scatter
//    scatter is required

int vas(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 0; i < count*8; i++) {
    a[ip[i]] = b[i];
  }
  return 0;
}

