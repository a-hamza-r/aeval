#include "declarations.h"

//    control loops
//    vector assignment, scatter
//    scatter is required

int vas(int count) {
  for (int i = 0; i < count*8; i++) {
    a[ip[i]] = b[i];
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	vas(count);
}