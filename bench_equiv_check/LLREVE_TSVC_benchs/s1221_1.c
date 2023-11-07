#include "declarations.h"

//	run-time symbolic resolution

int s1221(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 4; i < count*8; i++) {
    a[i] = a[i-4] + b[i];
  }
  return 0;
}
