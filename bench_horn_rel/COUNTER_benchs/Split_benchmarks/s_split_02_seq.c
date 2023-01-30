
int main()
{
  int x=0; int y=200; int z =400;
  while(y<400 && x<200) {
    y++;
    x++;
  }
  while(y<400 && x >= 200) {
    z = z+2;
    x++;
  }
  return 0;
}