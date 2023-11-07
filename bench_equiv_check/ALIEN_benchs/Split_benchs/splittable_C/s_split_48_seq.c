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
int s_split_48()
{
  int x=0;int y=0;
  while(x<5000 && x<4000) {
    y=y+1;
    x++;
  }
  while(x<5000 && x>=4000) {
    y=y+4;
    x++;
  }
  while(x>=5000 && x<6000) {
    y=y-4;
    x++;
  }
  while(x!=10000 && x>=5000 && x>=6000) {
    y=y-1;
    x++;
  }
  return 0;
}
int main()
{
return 0;
}
