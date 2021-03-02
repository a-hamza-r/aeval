#include <stdio.h>

int nondet();

int main()
{
	int i = 0;
	int bnd = nondet();
	while (bnd) {
		int arr[7] = {0, 1, 2, 3, 4, 5, 6}; 
		int j = 0;
		j += arr[i];
		i = j;
	}
}