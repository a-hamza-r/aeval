int main()
{
  int x=0;int y=8000; int z=0;
  while(x!=16000 && x<8000) {
    y=y-1;
    z=z+1;
    x=x+1;
  }
  while(x!=16000) {
    y=y+1;
    z=z-1;
    x=x+1;
  }
  return 0;
}
