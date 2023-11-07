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
extern int nondet();
int s_split_46()
{
  int x=0;int y=nondet();
  while(x<2000) {
    if(x/5<200) x=x+1;
    else x=x+5;
    if(x==1000) y=0;
  }
  return 0;
}
int main()
{
return 0;
}
