#include "seahorn/seahorn.h"
int main()
{
  int x=0; int y=0;
  while(x!=(2*1351235)) {
    if(x%2 == 0) y=y+1;
    x++;
  }
  sassert(y==1351235);
}
