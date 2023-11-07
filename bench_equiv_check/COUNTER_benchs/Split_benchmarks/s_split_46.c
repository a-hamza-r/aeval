extern int nondet();
int main()
{
  int x=0;int y=nondet();
  while(x<2000) {
    if(x/5<200) x=x+1;
    else x=x+5;
    if(x==1000) y=0;
  }
  return 0;
}
