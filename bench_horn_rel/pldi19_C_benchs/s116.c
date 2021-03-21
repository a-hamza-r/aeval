#include "declarations.h"


TYPE s116(int count) {
  for (int i = 0; i < count*8-5; i+=5) {
    a[i] = a[i + 1] * a[i];
    a[i + 1] = a[i + 2] * a[i + 1];
    a[i + 2] = a[i + 3] * a[i + 2];
    a[i + 3] = a[i + 4] * a[i + 3];
    a[i + 4] = a[i + 5] * a[i + 4];
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s116(count);
}