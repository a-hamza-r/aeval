int main()
{
  int x=0;
  while(x < 100000) {
    if(x==9998) x=1;
    else x= x+2;
  }
  return 0;
}
