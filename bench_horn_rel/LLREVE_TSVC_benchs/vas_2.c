#include "declarations.h"

//    control loops
//    vector assignment, scatter
//    scatter is required

int vas(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 0; i < count*8; i+=8) {
    a[ip[i]] = b[i];
    a[ip[i+1]] = b[i+1];
    a[ip[i+2]] = b[i+2];
    a[ip[i+3]] = b[i+3];
    a[ip[i+4]] = b[i+4];
    a[ip[i+5]] = b[i+5];
    a[ip[i+6]] = b[i+6];
    a[ip[i+7]] = b[i+7];
  }
  return 0;
}

