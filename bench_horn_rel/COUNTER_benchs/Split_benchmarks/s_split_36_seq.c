int main()
{
  int x=-10000;int y=0;
  while(x<0 && y>=x) {
    x=x+1;
    y=-1 * x;
  }
  while(x<0 && y<x) {
    y=y+2;
  }
  return 0;
}
