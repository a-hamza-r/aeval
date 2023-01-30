#include "seahorn/seahorn.h"
int main()
{
  int x=0;
  while(x < 10000) {
    if(x==9998) x=1;
    else x= x+2;
  }
  sassert(x<=9996);
}
