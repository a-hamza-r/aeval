#include "declarations.h"


TYPE vtvtv(int count) {
  for (int i = 0; i < count*8; i++) {
    a[i] *= b[i]*c[i];
  }
  return 0;
}


int nondet();

int main() {
  int count = nondet();
  vtvtv(count);
}