extern int nondet();
int main()
{
  int x=1000; int z=100;
  while(nondet()) {
    if((x/10)<z) x=x+1;
    else x=x-1;
    if((x/10)<z) z=z-1;
    else z=z+1;
  }
  return 0;
}
