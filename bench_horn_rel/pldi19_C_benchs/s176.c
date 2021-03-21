#include "declarations.h"


/** vectorizes with gcc */
TYPE s176(int count) {
  int m = count;
  for (int j = 0; j < m; j++) {
    for (int i = 0; i < m; i++) {
      a[i] += b[i+m-j-1] * c[j];
    }
  }
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s176(count);
}