extern int nondet();
int main()
{
  int x=0; int y=nondet(); int z=0;
  if(y<25) return 0;
  while(x<=(50*y) && y>(x/50)) {
    z=z+1;
    x = x+1;
  }
  while(x<=(50*y) && y<=(x/50)) {
    x = x+1;
  }
  return 0;
}
