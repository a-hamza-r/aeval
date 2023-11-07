#include "declarations.h"

//    search loops
//    if to last-1

TYPE s331(int count) {
  TYPE j = -1;
  for (int i = 0; i < count*8; i++) {
    if (a[i] < 0) {
      j = i;
    }
  }
  return j+1;
}


int nondet();

int main() {
	int count = nondet();
	s331(count);
}