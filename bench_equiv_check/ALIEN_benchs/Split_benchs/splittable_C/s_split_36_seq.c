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
int s_split_36()
{
  int x=-10000;int y=0;
  while(y>=x) {
    x=x+1;
    y=-1 * x;
  }
  while(x<0 && y<x) {
    y=y+2;
  }
  return 0;
}
int main()
{
return 0;
}
