#include "declarations.h"

//  induction variable recognition
//  induction variable with multiple increments

TYPE s127(int count) {
  int j = -1;
  for (int i = 0; i < count*4-1; i++) {
    j++;
    a[j] = b[i] + c[i] * d[i];
    j++;
    a[j] = b[i] + d[i] * e[i];
  }
  return 0;
}

/*after induction variable recognition

TYPE s127(int count) {
  for (int i = 0; i < count*4-1; i++) {
    a[2*i] = b[i] + c[i] * d[i];
    a[2*i+1] = b[i] + d[i] * e[i];
  }
  return 0;
}*/


int nondet();

int main() {
	int count = nondet();
	s127(count);
}