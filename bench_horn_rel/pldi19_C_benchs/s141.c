#include "declarations.h"


TYPE s141(int count) {
	int k;
	for (int i = 0; i < count; i++) {
		k = (i+1) * ((i+1) - 1) / 2 + (i+1)-1;
		for (int j = i; j < count; j++) {
			array[k] += bb[j][i];
			k += j+1;
		}
	}
  return 0;
}


int nondet();

int main() {
	int count = nondet();
	s141(count);
}