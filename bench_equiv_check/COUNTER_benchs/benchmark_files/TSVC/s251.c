#include "declarations.h"

//	scalar and array expansion
//	scalar expansion

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

/*TYPE s251(int count) {
  TYPE s;
  for (int i = 0; i < count*8; i++) {
   	s = b[i] + c[i] * d[i];
	 a[i] = s * s;
  }
  return 0;
}
*/

TYPE s251(int count) {
  TYPE s[count*8];
  for (int i = 0; i < count*8; i++) {
    s[i] = b[i] + c[i] * d[i];
    a[i] = s[i] * s[i];
  }
  return 0;
}

int main() {
	return 0;
}