#include "seahorn/seahorn.h"
extern int unknown1();
int main()
{
  int x=0; int y=unknown1(); int z=0;
  if(y<0) return 0;
  while(x<=(1000*(y+1))) {
    if(y==(x/1000)) z=z+1;
    x = x+1;
  }
  sassert(z==1000);
}
