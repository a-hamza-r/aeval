#include <stdio.h>

int nondet();

int foo(int i, int j)
{
	return i + j;
}

int bar(int i, int j)
{
	return i - j;
}

int main() 
{
	int i = nondet();
	int j = nondet();

	i = foo(i, j);
	j = bar(i, j);
	i = bar(i, j);

	return 0;
}