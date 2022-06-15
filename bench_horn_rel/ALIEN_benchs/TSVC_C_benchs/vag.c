#include "declarations.h"

//    control loops
//    vector assignment, gather
//    gather is required

int vag(int count) {
  for (int i = 0; i < count*8; i++) {
    a[i] = b[ip[i]];
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	vag(count);
}