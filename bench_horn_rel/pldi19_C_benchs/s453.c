#include "declarations.h"

//	induction varibale recognition

TYPE s453(int count) {
  TYPE s = 0;
  for (int i = 0; i < count*8; i++) {
    s += (TYPE)2;
    a[i] = s * b[i];
  }
  return 0;
}


/*after induction variable recognition:

TYPE s453(int count) {
  for (int i = 0; i < count*8; i++) {
    a[i] = 2*(i+1) * b[i];
  }
  return 0;
}*/


int nondet();

int main() {
	int count = nondet();
	s453(count);
}