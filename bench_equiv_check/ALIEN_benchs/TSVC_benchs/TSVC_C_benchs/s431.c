#include "declarations.h"

//    parameters
//    parameter statement

TYPE s431(int count) {
  int k1=1;
  int k2=2;
  int k=2*k1-k2;
  for (int i = 0; i < count*8; i++) {
    a[i] = a[i+k] + b[i];
  }
  return 0;
}


/*after partial transformation:
TYPE s431(int count) {
  int k=0;
  for (int i = 0; i < count*8; i++) {
    a[i] = a[i+k] + b[i];
  }
  return 0;
}*/


int nondet();

int main() {
	int count = nondet();
	s431(count);
}