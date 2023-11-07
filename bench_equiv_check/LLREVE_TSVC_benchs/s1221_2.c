#include "declarations.h"

//	run-time symbolic resolution

int s1221(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 4; i < count*8; i+=4) {
    a[i] = a[i-4] + b[i];
    a[i+1] = a[i+1-4] + b[i+1];
    a[i+2] = a[i+2-4] + b[i+2];
    a[i+3] = a[i+3-4] + b[i+3];
  }
  return 0;
}
