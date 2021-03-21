#include "declarations.h"

TYPE s115(int count) {
  for (int j = 0; j < count; j++) {
    for (int i = j+1; i < count; i++) {
      a[i] -= aa[j][i] * a[j];
    }
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s115(count);
}