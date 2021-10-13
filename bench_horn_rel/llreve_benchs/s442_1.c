#include "declarations.h"

//    non-logical if's
//    computed goto

int s442(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 0; i < count*8; i++) {
    switch (indx[i]) {
        case 1:  {  a[i] += b[i] * b[i];  break;  };
        case 2:  {  a[i] += c[i] * c[i];  break;  };
        case 3:  {  a[i] += d[i] * d[i];  break;  };
        case 4:  {  a[i] += e[i] * e[i];  break;  };
    }
  }
  return 0;
}

