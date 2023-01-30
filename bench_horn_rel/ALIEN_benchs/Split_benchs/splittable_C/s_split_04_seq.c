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
int s_split_04()
{
  int x=0; int y=0; int z =0;
  while(y<=x) {
    y=x+y;
    x++;
  }
  while(x<3452365 && y>x) {
    z=z+1;
    y=x+y;
    x++;
  }
  return 0;
}
int main()
{
return 0;
}
