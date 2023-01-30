extern int nondet();

int main()
{
  int x=nondet(); int z=nondet(); int v=0; int w=0;
  if(x<=z) return 0;
  while(v<=1000) {
    if(x<z) v=v+1;
    if(x>=z) w=w+1;
    x = x+1;
    z=z+2;
  }
  return 0;
}
