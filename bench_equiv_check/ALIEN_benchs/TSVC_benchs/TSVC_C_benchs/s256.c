#include "declarations.h"

//	scalar and array expansion
//	array expansion

TYPE s256(int count) {
	for (int i = 0; i < count*8; i++) {
		for (int j = 1; j < count*8; j++) {
			a[j] = 1 - a[j - 1];
			cc[j][i] = a[j] + bb[j][i]*d[j];
		}
	}
	return 0;
}

/*
//after interchanging 
TYPE s256(int count) {
	for (int j = 1; j < count*8; j++) {
		a[j] = 1 - a[j - 1];
		for (int i = 0; i < count*8; i++) {
			cc[j][i] = a[j] + bb[j][i]*d[j];
	 }
	}
	return 0;
}*/



int nondet();

int main() {
	int count = nondet();
	s256(count);
}