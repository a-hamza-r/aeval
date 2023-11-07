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

int s_split_02()
{
  int x=0; int y=200; int z =400;
  while(y<400) {
    if(x<200) y++;
    if(x<200) z=z;
    else z = z+2;
    x++;
  }
  return 0;
}
int main()
{
return 0;
}
