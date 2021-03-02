#include <stdio.h>

int nondet();

int main()
{
	int i = 0, j;
	int bnd = nondet();
	int arr[7] = {nondet(), nondet(), nondet(), nondet(), nondet(), nondet(), nondet()}; 
	while (bnd) {
		i++;
	}
	j = arr[0];
}