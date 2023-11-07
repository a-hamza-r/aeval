int main()
{
  int x=-100; int z=-100; int i = 0; int N = 105;
  while(i<N) {
    i++;
    if(z<4) z=z+1;
    else z=z%4;
    x++;
    x=x%5;
  }
}