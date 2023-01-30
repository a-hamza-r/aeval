extern int nondet();
int main()
{
  int x=1; int z=0;
  while(nondet()) {
    if(x%3 == 1) z=z+x;
    else z=z-x;
    x=-x;
  }
  return 0;
}
