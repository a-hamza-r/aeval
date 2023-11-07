int main()
{
  int x=-100; int z=-100; int i = 0; int N = 105;
  while(z<4) {
    i++;
    z=z+1;
    x++;
    x=x%5;
  }
  while(i<N && z>=4) {
    i++;
    z=z%4;
    x++;
    x=x%5;
  }
}