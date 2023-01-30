extern int nondet();
int main()
{
  int x=0; int y=10; int z=0;
  while(nondet()) {
    if(x==y) z=0;
    else z++;
    x = (x+1)%10;
    y = (y-1)%10;
  }
  return 0;
}
