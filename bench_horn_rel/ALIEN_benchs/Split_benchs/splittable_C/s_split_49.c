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
int s_split_49()
{
  int x=0;int y=0;
  while(x!=15000) {
    if(x>=7500){
      if(x>=12500)
        y=y-2;
      else
        y=y+1;
    }else{
      if(x>=2500)
        y=y+1;
      else
        y=y-2;
    }
    x++;
  }
  return 0;
}
int main()
{
return 0;
}
