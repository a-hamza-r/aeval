extern int nondet();
int main()
{
  int x=1000; int z=100;
  while(nondet() && (x/10)>=z) {
    x=x-1;
    z=z+1;
  }
  while(nondet() && (x/10)<z) {
    x=x+1;
    z=z-1;
  }
  return 0;
}
