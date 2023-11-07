int main()
{
  int x=0;int y=0;
  while(x<100000000 && x<50000000) {
    x++;
  }
  while(x<100000000 && x>=50000000) {
    y=y+1;
    x++;
  }
  return 0;
}
