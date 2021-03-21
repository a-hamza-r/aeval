#include "declarations.h"


TYPE s318(int count) {
  int k = 0;
  int index = 0;
  TYPE max = abs(a[0]);
  k++;

  for (int i = 0; i < count*8; i++) {
    if (abs(a[k]) <= max) {
      goto L5;
    }
    index = i;
    max = abs(a[k]);
L5:
		k++;
  }

  return max+index;
}


int nondet();

int main() {
  int count = nondet();
  s318(count);
}