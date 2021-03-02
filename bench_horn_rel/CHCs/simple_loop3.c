#include <stdio.h>

int nondet();

int main()
{
	int i = 0;
	int bnd = nondet(); 
	while (i < bnd) 
		i++;
}