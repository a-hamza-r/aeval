#include "declarations.h"


TYPE s315(int count) {
  TYPE x;
  int index;

  x = a[0];
  index = 0;
  for (int i = 0; i < count*8; i++) {
    if (a[i] > x) {
      x = a[i];
      index = i;
    }
  }

  return x + (TYPE)index;
}


int nondet();

int main() {
  int count = nondet();
  s315(count);
}