#include "declarations.h"

//	control flow
//	deriving assertions

TYPE s162(int count) {
  if (k > 0) {
    for (int i = 0; i < count*8-1; i++) {
      a[i] = a[i + k] + b[i] * c[i];
    }
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s162(count);
}