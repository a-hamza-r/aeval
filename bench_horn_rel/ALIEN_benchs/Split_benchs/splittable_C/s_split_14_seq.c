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
int s_split_14()
{
  int x=-100; int z=-100; int i = 0; int N = 105;
  while(z<4) {
    i++;
    z=z+1;
    x++;
    x=x%5;
  }
  while(i<N && z>=4) {
    i++;
    z=z%4;
    x++;
    x=x%5;
  }
}
int main()
{
return 0;
}
