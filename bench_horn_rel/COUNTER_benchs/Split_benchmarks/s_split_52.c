int main()
{
  int x=0;int c=5000; int y=c;
  while(x!=2*c) {
    if(x>=c) y=y+1;
    else y=y-1;
    x=x+1;
  }
  return 0;
}
