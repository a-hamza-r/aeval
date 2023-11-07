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
int s_split_44()
{
  int x=0;int y=1000; int z=2000;
  while(y<=2000) {
    if(y>=2000) z=z+1;
    if(x>=1000) y=y+1;
    x=x+1;
  }
  return 0;
}
int main()
{
return 0;
}
