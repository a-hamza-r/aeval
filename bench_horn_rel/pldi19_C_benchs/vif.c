#include "declarations.h"


TYPE vif(int count) {
  for (int i = 0; i < count*8; i++) {
    if(b[i] > 0)
      a[i] = b[i];
  }
  return 0;
}


int nondet();

int main() {
  int count = nondet();
  vif(count);
}