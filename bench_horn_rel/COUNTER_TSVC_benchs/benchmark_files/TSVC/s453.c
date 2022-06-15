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

//	induction varibale recognition

/*TYPE s453(int count) {
  TYPE s = 0;
  for (int i = 0; i < count*8; i++) {
    s += (TYPE)2;
    a[i] = s * b[i];
  }
  return 0;
}*/


TYPE s453(int count) {
  for (int i = 0; i < count*8; i++) {
    a[i] = 2*(i+1) * b[i];
  }
  return 0;
}

int main() {
	return 0;
}