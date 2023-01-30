int main()
{
  int x=0;int y=1000; int z=2000; int w=3000;
  while(z<=3000 && x<1000) {
    x++;
  }
  while(z<=3000 && x>=1000 && y<2000) {
    y=y+1;
    x++;
  }
  while(z<=3000 && x>=1000 && y>=2000 && z<3000) {
    y=y+1;
    z=z+1;
    x++;
  }
  while(z<=3000 && x>=1000 && y>=2000 && z>=3000) {
    y=y+1;
    z=z+1;
    w=w+1;
    x++;
  }
  return 0;
}
