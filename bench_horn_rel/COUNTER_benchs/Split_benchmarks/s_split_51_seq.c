int main()
{
  int x=0;int y=3333; int z=6666;
  while(x!=9999 && x<3333) {
    x=x+1;
  }
  while(x!=9999 && x>=3333 && y<6666) {
    y=y+1;
    x=x+1;
  }
  while(x!=9999 && x>=3333 && y>=6666) {
    z=z+1;
    y=y+1;
    x=x+1;
  }
  return 0;
}
