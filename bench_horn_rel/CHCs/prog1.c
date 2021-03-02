#include <stdio.h>

int nondet();

int main()
{
	int i = 0, j;
	int bnd = nondet();
	// int arr[7] = {0, 1, 2, 3, 4, 5, 6}; 
	// int arr2[7] = {7, 8, 9, 10, 11, 12, 13};
	int arr[7] = {1, 2, nondet(), nondet(), nondet(), nondet(), nondet()}; 
	int arr2[7] = {nondet(), nondet(), nondet(), nondet(), nondet(), 12, 13}; 
	while (bnd) {
		j = arr[i];
		arr[i] = arr2[i];
		arr2[i] = j;
		i++;
	}
}