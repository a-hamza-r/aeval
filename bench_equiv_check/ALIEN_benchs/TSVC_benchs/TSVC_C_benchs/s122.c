#include "declarations.h"

//	induction variable recognition
//	variable lower and upper bound, and stride
//	reverse data access and jump in data access

TYPE s122(int count) {
  int k = 0;
  for (int i = 1; i < count*8; i++) {
    k++;
    a[i] += b[count*8-k];
  }
  return 0;
}

/*vectorized: 

TYPE s122(int count) {
  // int k = 0;
  for (int i = 1; i < count*8; i++) {
    a[i] += b[count*8-i];
    a[(i+1)] += b[count*8-(i+1)];
    a[(i+2)] += b[count*8-(i+2)];
    a[(i+3)] += b[count*8-(i+3)];
    a[(i+4)] += b[count*8-(i+4)];
    a[(i+5)] += b[count*8-(i+5)];
    a[(i+6)] += b[count*8-(i+6)];
    a[(i+7)] += b[count*8-(i+7)];
  }
  return 0;
}*/


int nondet();

int main() {
	int count = nondet();
	s122(count);
}