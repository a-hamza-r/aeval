int main()
{
  int x=0;
  while(x<2000 && x/5<200) {
    x=x+1;
  }
  while(x<2000 && x/5>=200) {
    x=x+5;
  }
  return 0;
}
