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
int s_split_15()
{
  int x=0; int y=0; int z=0;
  do{
    z=z+2;
    x++;
    x=x%1000;
    y++;
  }while(x<500);
  while(x!=0 && x>=500) {
    x++;
    x=x%1000;
    y++;
  }
  return 0;
}
int main()
{
return 0;
}
