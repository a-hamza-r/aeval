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
int s_split_52()
{
  int x=0;int c=5000; int y=c;
  while(x<c) {
    y=y-1;
    x=x+1;
  }
  while(x!=2*c && x>=c) {
    y=y+1;
    x=x+1;
  }
  return 0;
}
int main()
{
return 0;
}
