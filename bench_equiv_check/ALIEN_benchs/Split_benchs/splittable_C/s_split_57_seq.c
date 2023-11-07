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
int s_split_57()
{
  int x=0;int y=1000; int z=2000; int w=3000;
  while(x<1000) {
    x++;
  }
  while(x>=1000 && y<2000) {
    y=y+1;
    x++;
  }
  while(x>=1000 && y>=2000 && z<3000) {
    y=y+1;
    z=z+1;
    x++;
  }
  while(z<=3000 && x>=1000 && y>=2000 && z>=3000) {
    y=y+1;
    z=z+1;
    w=w+1;
    x++;
  }
  return 0;
}
int main()
{
return 0;
}
