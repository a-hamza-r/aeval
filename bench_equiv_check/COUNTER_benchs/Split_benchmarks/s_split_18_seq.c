int main()
{
  int x=1; int y=1;
  while(x<=16 && y<16) {
    y=y*2;
    x = x*2;
  }
  while(x<=16 && y>=16) {
    y=x%16;
    x = x*2;
  }
  return 0;
}
