#include "declarations.h"

//    non-logical if's
//    computed goto

TYPE s442(int count) {
  for (int i = 0; i < count*8; i++) {
    switch (indx[i]) {
        case 1:  goto L15;
        case 2:  goto L20;
        case 3:  goto L30;
        case 4:  goto L40;
    }
L15:
      a[i] += b[i] * b[i];
      goto L50;
L20:
      a[i] += c[i] * c[i];
      goto L50;
L30:
      a[i] += d[i] * d[i];
      goto L50;
L40:
      a[i] += e[i] * e[i];
L50:
      ;
  }
  return 0;
}


/*after removing goto:
TYPE s442(int count) {
  for (int i = 0; i < count*8; i++) {
    switch (indx[i]) {
        case 1:  {  a[i] += b[i] * b[i];  break;  };
        case 2:  {  a[i] += c[i] * c[i];  break;  };
        case 3:  {  a[i] += d[i] * d[i];  break;  };
        case 4:  {  a[i] += e[i] * e[i];  break;  };
    }
  }
  return 0;
}*/


int nondet();

int main() {
	int count = nondet();
	s442(count);
}