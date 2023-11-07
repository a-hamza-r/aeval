int main()
{
  int x=0;int y=1000; int z=2000;
  while(y<=2000 && x<1000) {
    x=x+1;
  }
  while(y<=2000 && x>=1000 && y<2000) {
    y=y+1;
    x=x+1;
  }
  while(y<=2000 && x>=1000 && y>=2000) {
    z=z+1;
    y=y+1;
    x=x+1;
  }
  return 0;
}
