int main()
{
  int x=0;int y=0;
  while(x!=10000 && x<5000 && x<4000) {
    y=y+1;
    x++;
  }
  while(x!=10000 && x<5000 && x>=4000) {
    y=y+4;
    x++;
  }
  while(x!=10000 && x>=5000 && x<6000) {
    y=y-4;
    x++;
  }
  while(x!=10000 && x>=5000 && x>=6000) {
    y=y-1;
    x++;
  }
  return 0;
}
