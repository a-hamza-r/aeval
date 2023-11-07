#include "declarations.h"

//	scalar and array expansion
//	scalar expansion

TYPE s1251(int count) {
  TYPE s[count*8];
  for (int i = 0; i < count*8; i++) {
    s[i] = b[i]+c[i];
    b[i] = a[i]+d[i];
    a[i] = s[i]*e[i];
  }
  return 0;
}

/*after scalar expansion:

TYPE s1251(int count) {
  TYPE s[count*8];
  for (int i = 0; i < count*8; i++) {
    s[i] = b[i]+c[i];
    b[i] = a[i]+d[i];
    a[i] = s[i]*e[i];
  }
  return 0;
}*/


int nondet();

int main() {
  int count = nondet();
  s1251(count);
}