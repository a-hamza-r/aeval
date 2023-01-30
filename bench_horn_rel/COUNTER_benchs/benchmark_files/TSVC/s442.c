#include "declarations.h"

#include <stdlib.h>
#include <math.h>
#include <stdio.h>
#include <sys/param.h>
#include <sys/times.h>
#include <sys/types.h>
#include <time.h>
#include <malloc.h>
#include <string.h>
#include <assert.h>
#include "eqchecker_helper.h"

//    non-logical if's
//    computed goto

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
}

int main() {
    return 0;
}