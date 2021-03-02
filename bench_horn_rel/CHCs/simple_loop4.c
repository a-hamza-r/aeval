#include <stdio.h>

int nondet();

int main()
{
	int i = 0; 
	while (nondet()) 
		i = i + nondet();
}