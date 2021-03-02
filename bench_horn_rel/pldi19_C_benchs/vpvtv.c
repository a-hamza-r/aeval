#include "declarations.h"


TYPE vpvtv(int count) {
  for (int i = 0; i < count*8; i++) {
    a[i] += b[i]*c[i];
  }
  return 0;
}


int nondet();

int main() {
  int count = nondet();
  vpvtv(count);
}