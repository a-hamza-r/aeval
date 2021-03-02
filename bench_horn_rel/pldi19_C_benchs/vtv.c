#include "declarations.h"


TYPE vtv(int count) {
  for (int i = 0; i < count*8; i++) {
    a[i] *= b[i];
  }
  return 0;
}


int nondet();

int main() {
  int count = nondet();
  vtv(count);
}