#include "seahorn/seahorn.h"
int main()
{
  int x=1; int y=0; int z=0;
  while(x != 1 || y!=342341341) {
    if(x>0) y=y+1;
    if(x>0) z=z;
    else z=z+1;
    x=-x;
  }
  sassert(z==342341341);
}
