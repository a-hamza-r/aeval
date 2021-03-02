#include <stdio.h>

int nondet();

int main()
{
	int i = 0, j = 1, k = 2, l = 3;
	int bnd = nondet();
	int arr[4] = {1, 2, nondet(), nondet()}; 
	while (bnd < 10) {
		i++;
		j = i + 2;
		k = j * 10;
		l = arr[0] + arr[1] + arr[2] + arr[3];
	}
}