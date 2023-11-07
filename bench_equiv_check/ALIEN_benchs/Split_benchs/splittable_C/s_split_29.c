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
int s_split_29()
{
  int x=0; int y=0; int z=0; int w=0;
  while(x<=100) {
    if((y-(10*x))>0) z=z+1;
    if((y-(10*x))<=0) w=w+1;
    y=y+x;
    x = x+1;
  }
  return 0;
}
int main()
{
return 0;
}
