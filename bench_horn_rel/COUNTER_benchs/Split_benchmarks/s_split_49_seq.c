int main()
{
  int x=0;int y=0;
  while(x!=15000 && x<7500 && x<2500) {
    y=y-2;
    x++;
  }
  while(x!=15000 && x<7500 && x>=2500) {
    y=y+1;
    x++;
  }
  while(x!=15000 && x>=7500 && x<12500) {
    y=y+1;
    x++;
  }
  while(x!=15000 && x>=7500 && x>=12500) {
    y=y-2;
    x++;
  }
  return 0;
}
