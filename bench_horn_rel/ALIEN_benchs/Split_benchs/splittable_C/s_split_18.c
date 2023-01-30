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
int s_split_18()
{
  int x=1; int y=1;
  while(x<=16) {
    if(y<16) y=y*2;
    else y=x%16;
    x = x*2;
  }
  return 0;
}
int main()
{
return 0;
}
