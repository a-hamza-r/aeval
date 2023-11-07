extern int nondet();
int main()
{
  int x=nondet(); int y=nondet(); int z =nondet(); int v=0;
  if(x<=y) return 0;
  if(y<=z) return 0;
  while((z-x)<=72531 && x>=y) {
    x++;
    y=y+3;
    z=z+2;
  }
  while((z-x)<=72531 && x<y) {
    v=v+1;
    x++;
    y=y+3;
    z=z+2;
  }
  return 0;
}
