int main()
{
  int x=0; int y=0; int z =0;
  while(x<3452365 && y<=x) {
    y=x+y;
    x++;
  }
  while(x<3452365 && y>x) {
    z=z+1;
    y=x+y;
    x++;
  }
  return 0;
}
