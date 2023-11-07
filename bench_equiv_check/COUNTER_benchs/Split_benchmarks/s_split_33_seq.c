extern int nondet();
int main()
{
  int x=0;int y=0; int z=0;
  while(nondet()) {
    x = x+1;
    if((z/100)==(x/100)) z=z;
    else z=z+100;
    y=(y+1)%100;
  }
  return 0;
}
