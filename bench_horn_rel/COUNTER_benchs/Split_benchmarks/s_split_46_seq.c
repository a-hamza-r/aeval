extern int nondet();
int main()
{
  int x=0;int y=nondet();
  while(x<2000 && x/5<200) {
    x=x+1;
  }
  while(x<2000 && x/5>=200 && x==1000) {
    x=x+5;
    y=0;
  }
  while(x<2000 && x/5>=200 && x!=1000) {
    x=x+5;
  }
  return 0;
}
