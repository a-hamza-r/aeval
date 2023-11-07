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
  while(x!=10000) {
    if(x<5000){
      if(x>=4000)
        y=y+4;
      else
        y=y+1;
    }
    else{
      if(x>=6000)
        y=y-1;
      else
        y=y-4;
    }
    x++;
  }
  return 0;
}
int main()
{
return 0;
}
