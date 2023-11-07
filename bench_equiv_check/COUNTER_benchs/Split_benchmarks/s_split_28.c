extern int nondet();
int main()
{
  int x=0; int y=nondet(); int z=0;
  if(y<100) return 0;
  while(y!=0) {
    if(y<=(x/50)) z=z+1;
    x = x+1;
    y=y-1;
  }
  return 0;
}
