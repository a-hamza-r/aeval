int main()
{
  int x=0; int y=0; int z=0;
  do{
    z=z+2;
    x++;
    x=x%1000;
    y++;
  }while(x!=0 && x<500);
  while(x!=0 && x>=500) {
    x++;
    x=x%1000;
    y++;
  }
  return 0;
}
