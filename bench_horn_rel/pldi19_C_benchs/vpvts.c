#include "declarations.h"


TYPE vpvts(int count, TYPE k) {
  for (int i = 0; i < count*8; i++) {
    a[i] += b[i]*k;
  }
  return 0;
}


int nondet();
TYPE nondet1();

int main() {
  int count = nondet();
  TYPE k = nondet1();
  vpvts(count, k);
}