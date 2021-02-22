#include "declarations.h"


TYPE s121(int count) {
  for (int i = 0; i < count*8-1; i++) {
    a[i] = a[i+1] + b[i];
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s121(count);
}