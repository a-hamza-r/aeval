int main()
{
  int x=50000;int y=0;
  while(y<=50000 && y<x) {
    y=y+1;
  }
  while(y<=50000 && y>=x) {
    x=x+5;
  }
  return 0;
}
