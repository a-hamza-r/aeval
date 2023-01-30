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
int s_split_07()
{
  int x=nondet(); int y=nondet(); int z =nondet(); int v=0;
  if(x<=y) return 0;
  if(y<=z) return 0;
  while((z-x)<=72531) {
    if(x<y) v=v+1;
    x++;
    y=y+3;
    z=z+2;
  }
  return 0;
}
int main()
{
return 0;
}
