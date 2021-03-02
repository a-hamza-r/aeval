#include "declarations.h"


TYPE s1221(int count) {
  for (int i = 4; i < count*8; i++) {
    a[i] = a[i-4] + b[i];
  }
  return 0;
}


int nondet();

int main() {
  int count = nondet();
  s1221(count);
}