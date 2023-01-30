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

int s_split_17()
{
  int x=nondet(); int z=nondet(); int v=0; int w=0;
  if(x<=z) return 0;
  while(v<=1000) {
    if(x<z) v=v+1;
    if(x>=z) w=w+1;
    x = x+1;
    z=z+2;
  }
  return 0;
}
int main()
{
return 0;
}
