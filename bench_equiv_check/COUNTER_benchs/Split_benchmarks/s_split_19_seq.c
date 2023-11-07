int main()
{
  int x=1; int z=-1;
  while(x<=5143523 && x>=0){
    x = -2*x;
  }
  while(x<=5143523 && x<0){
    z=4*z;
    x = -2*x;
  }
  return 0;
}
