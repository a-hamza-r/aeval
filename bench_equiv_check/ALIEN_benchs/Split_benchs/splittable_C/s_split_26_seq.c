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
extern int nondet();
int s_split_26()
{
  int x=0; int y=nondet(); int z=0;
  if(y<25) return 0;
  while(y>(x/50)) {
    z=z+1;
    x = x+1;
  }
  while(x<=(50*y) && y<=(x/50)) {
    x = x+1;
  }
  return 0;
}
int main()
{
return 0;
}
