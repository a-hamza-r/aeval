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
  while(x/5<200) {
    x=x+1;
  }
  while(x/5>=200 && x==1000) {
    x=x+5;
    y=0;
  }
  while(x<2000 && x/5>=200 && x!=1000) {
    x=x+5;
  }
  return 0;
}
int main()
{
return 0;
}
